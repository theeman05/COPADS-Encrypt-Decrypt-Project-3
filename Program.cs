////////////////////////////////////////////////////////////////////////////////////////////////////////
//FileName: Program.cs
//Author : Ethan Hartman (ehh4525@rit.edu)
//Created On : 4/1/2024
//Last Modified On : 4/7/2024
//Description : Program to use network protocols to send secure messages to other people and decode messages sent to you.
////////////////////////////////////////////////////////////////////////////////////////////////////////

namespace System
{
    using System.Numerics;
    using System.Threading.Tasks;
    using System.Security.Cryptography;
    using System.IO;
    using System.Text.Json;
    using System.Text.Json.Serialization;
    using System.Text;

    /// <summary>
    /// Extension methods for the BigInteger class providing prime checking, factor, and sqrt calculating.
    /// </smmary>
    public static class BigIntegerPrimeExtensions
    {
        private static readonly BigInteger BIG_TWO = new(2);

        /// Generates a random BigInteger between the given min and max values.
        private static BigInteger RandomBigInteger(BigInteger minValue, BigInteger maxValue)
        {
            byte[] bytes = new byte[maxValue.ToByteArray().Length];
            using (RandomNumberGenerator rng = RandomNumberGenerator.Create())
            {
                rng.GetBytes(bytes);
            }
            return BigInteger.Remainder(new BigInteger(bytes), maxValue - minValue + 1) + minValue;
        }

        /// Determines if the given BigInteger is probably prime using the Miller-Rabin primality test.
        public static bool IsProbablyPrime(this BigInteger value, int k = 10)
        {
            if (value == 2 || value == 3)
                return true;
            else if (value <= 1 || value.IsEven)
                return false;

            // Quick check for small numbers
            int upper = value < 1000 ? (int) value : 1000;
            for (int i = 3; i < upper; i += 2)
                if (value % i == 0)
                    return false;

            BigInteger r = 0, d = value - 1;
            while (d % 2 == 0)
            {
                d /= 2;
                r++;
            }

            for (int i = 0; i < k; i++)
            {
                BigInteger rand = RandomBigInteger(BIG_TWO, value - 2);
                BigInteger x = BigInteger.ModPow(rand, d, value);

                if (x == 1 || x == value - 1)
                    continue;

                for (BigInteger j = 0; j < r - 1; j++)
                {
                    x = BigInteger.ModPow(x, BIG_TWO, value);

                    if (x == 1)
                        return false;

                    if (x == value - 1)
                        break;
                }

                if (x != value - 1)
                    return false;
            }

            return true;
        }

        /// Calculates the modular inverse of the given BigInteger.
        public static BigInteger ModInverse(this BigInteger a, BigInteger b)
        {
            BigInteger i = b, v = 0, d = 1;
            while (a > 0)
            {
                BigInteger z = i / a, x = a;
                a = i % x;
                i = x;
                x = d;
                d = v - z * x;
                v = x;
            }
            v %= b;
            if (v < 0) v = (v + b) % b;
            return v;
        }
    }
    
    /// <summary>
    /// Interface for objects that can be converted to JSON.
    /// </summary>
    interface IJsonable
    {
        /// Converts the object to a JSON string.
        public string ToJson();
    }

    /// <summary>
    /// Interface for objects that can be sent to the server.
    /// </summary>
    interface IEmailable : IJsonable
    {
        public string email { get; set; }

        /// Gets the endpoint for the object.
        public abstract string GetEndpoint();
    }

    /// <summary>
    /// Base class for keys that can be stored and retrieved from the local filesystem.
    /// </summary>
    abstract class KeyBase : IJsonable
    {
        private static readonly int ENCRYPTION_BYTE_SIZE = 4;
        public string key { get; } /// The base64 encoded key string for the class.

        public abstract string ToJson();

        /// Gets the save location for the key file.
        public static string GetSaveLocation(string fileName)
        {
            return Path.Combine(Environment.CurrentDirectory, fileName + ".key");
        }

        /// Parses the key from the directory if it exists. Otherwise, returns null.
        public static T? ParseFromDirectory<T>(string fileName = "") where T : KeyBase
        {
            if (string.IsNullOrWhiteSpace(fileName)) 
                fileName = typeof(T).Name.ToLower()[..^3];
            string filePath = GetSaveLocation(fileName);
            return File.Exists(filePath) ? JsonSerializer.Deserialize<T>(File.ReadAllText(filePath)) : default;
        }

        /// Creates and encrpyts a key from the given eOrD and n values.
        public KeyBase(BigInteger eOrD, BigInteger n)
        {
            byte[] eOrDBytes = eOrD.ToByteArray();
            byte[] nBytes = n.ToByteArray();

            // Reverse byte order because eOrD and n are little-endian
            Array.Reverse(eOrDBytes);
            Array.Reverse(nBytes);

            // Get the big-endian size of the byte arrays
            byte[] eOrDSizeBytes = BitConverter.GetBytes(eOrDBytes.Length);
            byte[] nSizeBytes = BitConverter.GetBytes(nBytes.Length);

            // Allocate a byte array for the key bytes
            byte[] keyBytes = new byte[ENCRYPTION_BYTE_SIZE + eOrDBytes.Length + ENCRYPTION_BYTE_SIZE + nBytes.Length];

            // Copy stuff over to keyBytes in their respective order
            Array.Copy(eOrDSizeBytes, 0, keyBytes, 0, ENCRYPTION_BYTE_SIZE);
            Array.Copy(eOrDBytes, 0, keyBytes, ENCRYPTION_BYTE_SIZE, eOrDBytes.Length);
            Array.Copy(nSizeBytes, 0, keyBytes, ENCRYPTION_BYTE_SIZE + eOrDBytes.Length, ENCRYPTION_BYTE_SIZE);
            Array.Copy(nBytes, 0, keyBytes, ENCRYPTION_BYTE_SIZE + eOrDBytes.Length + ENCRYPTION_BYTE_SIZE, nBytes.Length);

            key = Convert.ToBase64String(keyBytes);
        }
        
        /// Creates a key from the given encrypted base64 encoded string.
        public KeyBase(string key)
        {
            this.key = key;
        }

        /// Stores the key to the local filesystem.
        public void Store(string fileName = "")
        {
            if (string.IsNullOrWhiteSpace(fileName)) 
                fileName = GetType().Name.ToLower()[..^3];
            File.WriteAllText(GetSaveLocation(fileName), ToJson());
        }

        /// Extracts the key from the base64 encoded string.
        public void ExtractKey(out BigInteger eOrD, out BigInteger n)
        {
            byte[] keyBytes = Convert.FromBase64String(key);

            // Extract size of eOrD
            byte[] eOrDSizeBytes = new byte[ENCRYPTION_BYTE_SIZE];
            Array.Copy(keyBytes, 0, eOrDSizeBytes, 0, ENCRYPTION_BYTE_SIZE);

            int eOrDSize = BitConverter.ToInt32(eOrDSizeBytes, 0);

            // Extract eOrD bytes
            byte[] eOrDBytes = new byte[eOrDSize];
            Array.Copy(keyBytes, ENCRYPTION_BYTE_SIZE, eOrDBytes, 0, eOrDSize);

            // Extract size of n
            byte[] nSizeBytes = new byte[ENCRYPTION_BYTE_SIZE];
            Array.Copy(keyBytes, ENCRYPTION_BYTE_SIZE + eOrDSize, nSizeBytes, 0, ENCRYPTION_BYTE_SIZE);
            int nSize = BitConverter.ToInt32(nSizeBytes, 0);

            // Extract n bytes
            byte[] nBytes = new byte[nSize];
            Array.Copy(keyBytes, ENCRYPTION_BYTE_SIZE + eOrDSize + ENCRYPTION_BYTE_SIZE, nBytes, 0, nSize);

            // Reverse byte order because E/D and N are little-endian
            Array.Reverse(eOrDBytes);
            Array.Reverse(nBytes);

            // Populate BigIntegers from byte arrays
            eOrD = new BigInteger(eOrDBytes);
            n = new BigInteger(nBytes);
        }
    }

    /// <summary>
    /// Class for the private key that can be stored and retrieved from the local filesystem.
    /// </summary>
    class PrivateKey : KeyBase
    { 
        public HashSet<string> email { get; set; }

        public PrivateKey(BigInteger e, BigInteger n) : base(e, n)
        {
            email = new HashSet<string>();
        }

        [JsonConstructor]
        public PrivateKey(string key, HashSet<string> email) : base(key) 
        {
            this.email = email;
        }

        /// Saves the email to the private key if it doesn't already exist.
        public static void SaveEmail(string email)
        {
            // Save the email to the private key if it exists.
            PrivateKey privateKey = ParseFromDirectory<PrivateKey>() ?? throw new KeyNotFoundException();
            if (privateKey.email.Add(email) == true)
                privateKey.Store();
        }
        
        /// Checks if the private key has the email.
        public static bool HasEmail(string email)
        {
            return ParseFromDirectory<PrivateKey>()?.email.Contains(email) ?? false;
        }

        public override string ToJson()
        {
            return JsonSerializer.Serialize(this);
        }
    }

    /// <summary>
    /// Class for the public key that can be stored and retrieved from the local filesystem.
    /// </summary>
    class PublicKey : KeyBase, IEmailable
    {
        public static readonly string ENDPOINT = "Key";
        public string email { get; set; }

        public PublicKey(BigInteger d, BigInteger n) : base(d, n) 
        {
            email = string.Empty;
        }

        [JsonConstructor]
        public PublicKey(string key, string email) : base(key) 
        { 
            this.email = email;
        }
        
        public override string ToJson()
        {
            return JsonSerializer.Serialize(this);
        }

        public string GetEndpoint()
        {
            return ENDPOINT;
        }
    }

    /// <summary>
    /// Class for a message.
    /// </summary>
    class Message : IEmailable
    {
        public static readonly string ENDPOINT = "Message";
        public string email { get; set; }
        public string content { get; } // Encrypted 64-bit encoded message
        public string messageTime { get { return DateTime.UtcNow.ToString("yyyy-MM-ddTHH:mm:ss"); } }

        public Message(string email, BigInteger encryptedMessage)
        {
            this.email = email;
            content = Convert.ToBase64String(encryptedMessage.ToByteArray());
        }

        [JsonConstructor]
        public Message(string email, string content, string messageTime)
        {
            this.email = email;
            this.content = content;
        }

        public string ToJson()
        {
            return JsonSerializer.Serialize(this);
        }

        public string GetEndpoint()
        {
            return ENDPOINT;
        }
    }

    /// <summary>
    /// Class for the server interface that can send and retrieve objects from the server.
    /// </summary>
    class ServerInterface
    {
        private static readonly string SERVER_URL = "http://voyager.cs.rit.edu:5050";
        private static readonly HttpClient CLIENT = new();

        /// Retrieves an object of type T from the server. Returns null if the object doesn't exist.
        public static async Task<T?> GetTAsync<T>(string endpoint, string email)
        {
            string response = await CLIENT.GetStringAsync($"{SERVER_URL}/{endpoint}/{email}");
            if (!string.IsNullOrEmpty(response))
                return JsonSerializer.Deserialize<T>(response);
            return default;
        }

        /// Sends an IEmailable object to the server.
        public static async Task SendEmailable(IEmailable emailable)
        {
            try
            {
                await CLIENT.PutAsync($"{SERVER_URL}/{emailable.GetEndpoint()}/{emailable.email}", new StringContent(emailable.ToJson(), Encoding.UTF8, "application/json"));
            }
            catch (Exception)
            {
                Console.WriteLine("There was an error sending your IEmailable.\nPlease try again later.");
            }
        }
    }

    /// <summary>
    /// Class for the messenger that can generate keys, send keys, get keys, send messages, and get messages.
    /// </summary>
    class Messenger
    {
        private static readonly int BATCH_SIZE = 500, E_BYTE_SIZE = 16;

        /// Generates a probably prime number of size <byteCount> bits.
        public static BigInteger GenerateProbablyPrime(RandomNumberGenerator rng, int byteCount)
        {
            BigInteger? probablyPrime = null;
            while (probablyPrime == null)
            {
                Task.Run(() => { // Utilizes thread pool for parallel generation
                    byte[] randomBytes = new byte[byteCount];
                    for (int i = 0; i < BATCH_SIZE && probablyPrime == null; i++)
                    {
                        rng.GetBytes(randomBytes);

                        BigInteger bigInt = BigInteger.Abs(new(randomBytes));
                        if (bigInt.IsEven && bigInt != 2) bigInt++; // Ensure we have an odd number to reduce time.
                        if (bigInt.IsProbablyPrime()) probablyPrime = bigInt;
                    }
                });
            }

            return (BigInteger) probablyPrime;
        }

        /// Generates a keypair of size <keySize> bits and stores it locally on the disk.
        public static void GenerateKey(int keySize)
        {
            // Key size must be positive, and a multiple of 8 starting at 32, and less than or eq to 2^16.
            if (keySize < 32 || keySize > Math.Pow(2, 16) || keySize % 8 != 0 )
                throw new Exception();

            keySize /= 8; // Convert bits to bytes

            // Generate prime numbers.
            RandomNumberGenerator rng = RandomNumberGenerator.Create();
            byte[] randN = new byte[1];
            rng.GetBytes(randN);

            // Get the directional sign for size
            int sign = randN[0] / byte.MaxValue <= .5 ? -1 : 1;
            rng.GetBytes(randN); // Get a random number for us to calculate size with.
            int pSize = (int)(keySize * (double)(.5 + sign * (.2 + .1 * randN[0] / byte.MaxValue)));

            // Initialize to 2 to avoid null checks lol.
            BigInteger d, t, n, e, p, q;
            d = t = n = e = p = q = 2;

            // Ensure that t is not divisible by e. We need to do this because the numbers are only probably prime
            while (t % e == 0)
            {
                // Asynchronusly run number gens
                Task[] tasks = {
                    Task.Run(() => { p = GenerateProbablyPrime(rng, pSize); }),
                    Task.Run(() => { q = GenerateProbablyPrime(rng, keySize - pSize); }),
                    Task.Run(() => { e = GenerateProbablyPrime(rng, E_BYTE_SIZE); })
                };

                // Wait for tasks to complete
                foreach (Task task in tasks)
                    while (!task.IsCompleted) { }

                t = (p - 1) * (q - 1);
            }

            rng.Dispose();

            // Calculate n and d for RSA encryption.
            n = p * q;
            d = e.ModInverse(t);

            // Store the keypairs locally on the disk.
            new PublicKey(e, n).Store();
            new PrivateKey(d, n).Store();
        }

        /// Send the public key for the given email to the server.
        public static async Task SendKeyAsync(string email)
        {
            // Retrieve the public key from the local disk (maybe).
            PublicKey? publicKey = KeyBase.ParseFromDirectory<PublicKey>();
            if (publicKey != null) // Is on disk and we have the file with the key for the given email.
            {
                // Try to save the email to the private key.
                try { PrivateKey.SaveEmail(email); }
                catch (KeyNotFoundException)
                {
                    Console.WriteLine("No private key found on disk. Please generate a keypair using the keyGen option first.");
                    return;
                }

                // Apply the given email but don't save it.
                publicKey.email = email;

                // Send the public key to the server.
                await ServerInterface.SendEmailable(publicKey);

                Console.WriteLine("Key saved");
            }
            else Console.WriteLine("No public key found on disk. Please generate a keypair using the keyGen option first.");
        }

        /// Retrieve the public key for the given email from the server and store it to the local filesystem.
        public static async Task GetKeyAsync(string email)
        {
            // Retrieve the public key for the given email from the server.
            PublicKey? publicKey = await ServerInterface.GetTAsync<PublicKey>(PublicKey.ENDPOINT, email);
            if (publicKey != null) 
                publicKey.Store(email); // Save the public key to the local disk with the email.
            else 
                Console.WriteLine($"No public key found on the server for '{email}'.");
        }

        /// Encrypts, encodes, then sends a message to the server.
        public static async Task SendMsgAsync(string email, string plaintext)
        {
            // Retrieve the public key for the given email from the local disk.
            PublicKey? publicKey = KeyBase.ParseFromDirectory<PublicKey>(email);
            if (publicKey != null) // Is on disk and we have the file with the key for the given email.
            {
                // Extract key e and n from the public key.
                publicKey.ExtractKey(out BigInteger e, out BigInteger n);

                // Encrypt the plaintext message using the public key. (plaintext^e mod n = ciphertext)
                BigInteger encryptedMsg = BigInteger.ModPow(new(Encoding.UTF8.GetBytes(plaintext)), e, n);

                // Send the encrypted message to the server.
                await ServerInterface.SendEmailable(new Message(email, encryptedMsg));

                Console.WriteLine("Message written");
            }
            else Console.WriteLine($"No public key found on disk for '{email}'. Please download this user's key using 'getKey'.");
        }

        /// Retrieves a message for the given email from the server and decrypts it.
        public static async Task GetMsgAsync(string email)
        {
            // Check if we have the user email in the private key.
            if (PrivateKey.HasEmail(email))
            {
                // Retrieve our private key from the local disk to decode.
                PrivateKey? privateKey = KeyBase.ParseFromDirectory<PrivateKey>();
                if (privateKey != null)
                {
                    // Retrieve the message from the server.
                    Message? message = await ServerInterface.GetTAsync<Message>(Message.ENDPOINT, email);
                    if (message != null && message.content != null)
                    {
                        // Extract key d and n from the private key.
                        privateKey.ExtractKey(out BigInteger d, out BigInteger n);

                        // Decrypt the message using the private key and display after converting to string. (ciphertext^d mod n = plaintext)
                        Console.WriteLine(Encoding.UTF8.GetString(BigInteger.ModPow(new(Convert.FromBase64String(message.content)), d, n).ToByteArray()));
                    }
                    else Console.WriteLine($"No message found on the server for '{email}'.");
                }
                else Console.WriteLine($"There was an error getting the message for '{email}'.");
            }
            else Console.WriteLine($"Cannot decrpyt message for '{email}'. You must get a new key for this user.");
        }
    }

    /// <summary>
    /// Main program class for the Messenger program.
    /// </summary>
    class Program
    {
        /// <summary>
        ///  Dictionary of optional arguments for the program. The list contains the name of the argument, and the description of the argument.
        /// </summary>
        private static readonly Dictionary<string, string[]> OPTIONAL_ARGS = new()
        {
            { "keyGen", new string[] { "keysize", "Generates a keypair of size <keysize> bits and store them locally on the disk, in the current directory" } },
            { "sendKey", new string[] { "email", "Sends the public key that was generated in the keyGen phase to the server, with the <email> address given" } },
            { "getKey", new string[] { "email", "Retrieves the public key for a particular user's <email>, and stores the key locally on the disk, in the current directory" } },
            { "sendMsg", new string[] { "email", "plaintext", "Takes a <plaintext> message, encrypts it using the public key of the person you are sending it to, based on their <email> address" } },
            { "getMsg", new string[] { "email", "Retrieves a message for a particular user's <email> if you have the private key" } }
        };

        /// Concatenates the optional parameters for the user to see.
        private static string ConcatOptionalParams(string[] values)
        {
            string parameters = "";
            for (int i = 0; i < values.Length - 1; i++)
                parameters += $"<{values[i]}> ";

            return parameters;
        }

        /// Length validates the optional arguments provided by the user and returns true if they're good, false o/w.
        private static bool ValidateOptionalArgs(string[] args)
        {
            // Invalid / no option provided.
            if (args.Length == 0 || !OPTIONAL_ARGS.TryGetValue(args[0], out string[]? value))
            {
                Console.WriteLine("Usage: Messenger <option> <other arguments>\nList of valid options:");
                foreach (var arg in OPTIONAL_ARGS)
                {
                    Console.WriteLine($"- {arg.Key}: {ConcatOptionalParams(arg.Value)}- {arg.Value.Last()}");
                }
            }
            else if (value.Length != args.Length) // Invalid number of parameters provided.
            {
                Console.WriteLine($"Invalid number of parameters specified for {args[0]}. Usage: Messenger <{args[0]}> {ConcatOptionalParams(value)}");
            }
            else return true;
            return false;
        }

        /// Main method for the program.
        public static async Task Main(string[] args)
        {
            if (ValidateOptionalArgs(args))
            {
                switch (args[0])
                {
                    case "keyGen":
                        try
                        {
                            Messenger.GenerateKey(int.Parse(args[1]));
                        }
                        catch (Exception) // If we have an exception, the key size is invalid.
                        {
                            Console.WriteLine("Invalid key size: Must be a positive integer divisible by 8 in the range [32, 2^16]");
                        }
                        break;
                    case "sendKey":
                        await Messenger.SendKeyAsync(args[1]);
                        break;
                    case "getKey":
                        await Messenger.GetKeyAsync(args[1]);
                        break;
                    case "sendMsg":
                        await Messenger.SendMsgAsync(args[1], args[2]);
                        break;
                    case "getMsg":
                        await Messenger.GetMsgAsync(args[1]);
                        break;
                }
            }
        }
    }
}