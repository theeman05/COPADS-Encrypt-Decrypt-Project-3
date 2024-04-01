////////////////////////////////////////////////////////////////////////////////////////////////////////
//FileName: Program.cs
//Author : Ethan Hartman (ehh4525@rit.edu)
//Created On : 4/1/2024
//Last Modified On : 4/1/2024
//Description : Program to use network protocols to send secure messages to other people and decode messages sent to you.
////////////////////////////////////////////////////////////////////////////////////////////////////////

namespace System
{
    using System.Numerics;
    using System.Threading.Tasks;
    using System.Security.Cryptography;
    using System.IO;
    using System.Text.Json;

    /// <summary>
    /// Extension methods for the BigInteger class providing prime checking, factor, and sqrt calculating.
    /// </smmary>
    public static class BigIntegerPrimeExtensions
    {
        private static readonly BigInteger BIG_TWO = new(2);

        private static BigInteger RandomBigInteger(BigInteger minValue, BigInteger maxValue)
        {
            byte[] bytes = new byte[maxValue.ToByteArray().Length];
            using (RandomNumberGenerator rng = RandomNumberGenerator.Create())
            {
                rng.GetBytes(bytes);
            }
            return BigInteger.Remainder(new BigInteger(bytes), maxValue - minValue + 1) + minValue;
        }

        public static bool IsProbablyPrime(this BigInteger value, int k = 10)
        {
            if (value == 2 || value == 3)
                return true;
            else if (value <= 1 || value.IsEven)
                return false;

            // Quick check for small numbers
            int upper = value < 1000 ? (int)value : 1000;
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

    class PrivateKey
    {
        string[] email { get; }
        string key { get; }

        static PrivateKey ParseFromDirectory()
        {
            return Program.DeserializeFromFile<PrivateKey>(Path.Combine(Environment.CurrentDirectory, "private.key"));
        }

        public PrivateKey(string key)
        {
            this.email = Array.Empty<string>();
            this.key = key;
        }

        public void Store()
        {
            Program.SerializeToFile(this, Path.Combine(Environment.CurrentDirectory, "private.key"));
        }
    }

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

        private static readonly int BATCH_SIZE = 500;

        public static void SerializeToFile<T>(T obj, string filePath)
        {
            File.WriteAllText(filePath, JsonSerializer.Serialize(obj));
        }

        public static T DeserializeFromFile<T>(string filePath)
        {
            if (File.Exists(filePath))
                return JsonSerializer.Deserialize<T>(File.ReadAllText(filePath));
            else
                throw new FileNotFoundException($"File not found: {filePath}");
        }

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
                return false;
            }
            else if (value.Length != args.Length) // Invalid number of parameters provided.
            {
                Console.WriteLine($"Invalid number of parameters specified for {args[0]}. Usage: Messenger <{args[0]}> {ConcatOptionalParams(value)}");
            }

            return true;
        }

        /// Generates a keypair of size <keySize> bits and stores it locally on the disk.
        private static void KeyGen(int keySize) // TODO
        {
            if (keySize < 32 || keySize > Math.Pow(2, 16)) // Key size must be positive, and a multiple of 8 starting at 32, and less than or eq to 2^16.
                throw new Exception();

            RandomNumberGenerator rng = RandomNumberGenerator.Create();
            BigInteger? probablyPrimeKey = null;
            while (probablyPrimeKey == null)
            {
                Task.Run(() => { // Utilizes thread pool for parallel generation
                    byte[] randomBytes = new byte[keySize];
                    for (int i = 0; i < BATCH_SIZE && probablyPrimeKey == null; i++)
                    {
                        rng.GetBytes(randomBytes);

                        BigInteger bigInt = BigInteger.Abs(new(randomBytes));
                        if (bigInt.IsEven && bigInt != 2) bigInt++; // Ensure we have an odd number to reduce time.
                        if (bigInt.IsProbablyPrime()) probablyPrimeKey = bigInt;
                    }
                });
            }
            rng.Dispose();

            // Step 2: Store the keypair locally on the disk.
        }

        private static void SendKey(string email) // TODO
        {
            // Step 1: Retrieve the public key from the local disk.
            if (true) // Is on disk and we have the file with the key for the given email.
            {
                // Step 2: Send the public key to the server.
            }
            else Console.WriteLine("No public key found on disk. Please generate a keypair using the keyGen option first.");
        }

        private static void GetKey(string email) // TODO
        {
            // Step 1: Retrieve the public key for the given email from the server.
            // Step 2: Store the key locally on the disk.
        }

        private static void SendMsg(string email, string plaintext) // TODO
        {
            // Step 1: Retrieve the public key for the given email from the local disk.
            if (true) // Is on disk and we have the file with the key for the given email.
            {
                // Step 2: Encrypt the plaintext message using the public key.
                // Step 3: Send the encrypted message to the server.
            }
            else Console.WriteLine("No public key found on disk. Please generate a keypair using the keyGen option first.");
        }

        private static void GetMsg(string email) // TODO
        {
            // Step 1: Retrieve the private key for the given email from the local disk.
            if (true) // Is on disk and we have the file with the key for the given email.
            {
                // Step 2: Retrieve the message from the server.
                // Step 3: Decrypt the message using the private key.
            }
            else Console.WriteLine("No private key found on disk. Please generate a keypair using the keyGen option first.");
        }

        public static void Main(string[] args)
        {
            args = new string[] { "keyGen", "128" };
            if (ValidateOptionalArgs(args))
            {
                switch (args[0])
                {
                    case "keyGen":
                        try
                        {
                            KeyGen(int.Parse(args[1]));
                        }
                        catch (Exception) // If we have an exception, the key size is invalid.
                        {
                            Console.WriteLine("Invalid key size: Must be a positive integer in the range [32, 2^16]\n");
                        }
                        break;
                    case "sendKey":
                        SendKey(args[1]);
                        break;
                    case "getKey":
                        GetKey(args[1]);
                        break;
                    case "sendMsg":
                        SendMsg(args[1], args[2]);
                        break;
                    case "getMsg":
                        GetMsg(args[1]);
                        break;
                }
            }
        }
    }
}