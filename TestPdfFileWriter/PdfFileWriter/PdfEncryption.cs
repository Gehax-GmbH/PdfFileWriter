/////////////////////////////////////////////////////////////////////
//
//	PdfFileWriter II
//	PDF File Write C# Class Library.
//
//	PdfEncryption
//	Support for AES-128 encryption
//
//	Author: Uzi Granot
//	Original Version: 1.0
//	Date: April 1, 2013
//	Major rewrite Version: 2.0
//	Date: February 1, 2022
//	Copyright (C) 2013-2022 Uzi Granot. All Rights Reserved
//
//	PdfFileWriter C# class library and TestPdfFileWriter test/demo
//  application are free software. They are distributed under the
//  Code Project Open License (CPOL-1.02).
//
//	The main points of CPOL-1.02 subject to the terms of the License are:
//
//	Source Code and Executable Files can be used in commercial applications;
//	Source Code and Executable Files can be redistributed; and
//	Source Code can be modified to create derivative works.
//	No claim of suitability, guarantee, or any warranty whatsoever is
//	provided. The software is provided "as-is".
//	The Article accompanying the Work may not be distributed or republished
//	without the Author's consent
//
//	The document PdfFileWriterLicense.pdf contained within
//	the distribution specify the license agreement and other
//	conditions and notes. You must read this document and agree
//	with the conditions specified in order to use this software.
//
//	For version history please refer to PdfDocument.cs
//
/////////////////////////////////////////////////////////////////////

using System.Data.Common;
using System.Numerics;
using System.Reflection.Emit;
using System.Security.Cryptography;
using System.Text;

namespace PdfFileWriter
	{
	/// <summary>
	/// Encryption type enumeration
	/// </summary>
	public enum EncryptionType
		{
		/// <summary>
		/// AES 128 bits
		/// </summary>
		Aes128,
        /// <summary>
        /// AES 256 bits
        /// </summary>
        Aes256,
        /// <summary>
        /// Standard 128 bits
        /// </summary>
        Standard128,
		}

	/// <summary>
	/// PDF reader permission flags enumeration
	/// </summary>
	/// <remarks>
	/// PDF reference manual version 1.7 Table 3.20 
	/// </remarks>
	public enum Permission
		{
		/// <summary>
		/// No permission flags
		/// </summary>
		None = 0,

		/// <summary>
		/// Low quality print (bit 3)
		/// </summary>
		LowQalityPrint = 4,

		/// <summary>
		/// Modify contents (bit 4)
		/// </summary>
		ModifyContents = 8,

		/// <summary>
		/// Extract contents (bit 5)
		/// </summary>
		ExtractContents = 0x10,

		/// <summary>
		/// Annotation (bit 6)
		/// </summary>
		Annotation = 0x20,

		/// <summary>
		/// Interactive (bit 9)
		/// </summary>
		Interactive = 0x100,

		/// <summary>
		/// Accessibility (bit 10)
		/// </summary>
		Accessibility = 0x200,

		/// <summary>
		/// Assemble document (bit 11)
		/// </summary>
		AssembleDoc = 0x400,

		/// <summary>
		/// Print (bit 12 plus bit 3)
		/// </summary>
		Print = 0x804,

		/// <summary>
		/// All permission bits (3, 4, 5, 6, 9, 10, 11, 12)
		/// </summary>
		All = 0xf3c,
		}

	////////////////////////////////////////////////////////////////////
	/// <summary>
	/// PDF encryption class
	/// </summary>
	/// <remarks>
	/// <para>
	/// For more information go to <a href="http://www.codeproject.com/Articles/570682/PDF-File-Writer-Csharp-Class-Library-Version#EncryptionSupport">2.6 Encryption Support</a>
	/// </para>
	/// </remarks>
	////////////////////////////////////////////////////////////////////
	public class PdfEncryption : PdfObject, IDisposable
		{
		private const int PermissionBase = unchecked((int) 0xfffff0c0);

		internal int Permissions;
		internal EncryptionType EncryptionType;
		internal byte[] MasterKey;
		internal MD5 MD5 = MD5.Create();
		
		//internal AesCryptoServiceProvider AES = new AesCryptoServiceProvider();
		internal Aes AES = Aes.Create();

		private static readonly byte[] PasswordPad =
			{
			(byte) 0x28, (byte) 0xBF, (byte) 0x4E, (byte) 0x5E, (byte) 0x4E, (byte) 0x75, (byte) 0x8A, (byte) 0x41,
			(byte) 0x64, (byte) 0x00, (byte) 0x4E, (byte) 0x56, (byte) 0xFF, (byte) 0xFA, (byte) 0x01, (byte) 0x08,
			(byte) 0x2E, (byte) 0x2E, (byte) 0x00, (byte) 0xB6, (byte) 0xD0, (byte) 0x68, (byte) 0x3E, (byte) 0x80,
			(byte) 0x2F, (byte) 0x0C, (byte) 0xA9, (byte) 0xFE, (byte) 0x64, (byte) 0x53, (byte) 0x69, (byte) 0x7A
			};

		private static readonly byte[] Salt = { (byte) 0x73, (byte) 0x41, (byte) 0x6c, (byte) 0x54 };

		/// <summary>
		/// AES256
		/// </summary>
        bool isPdf2 = false;
		int CBCBlockSize = 128;

        ////////////////////////////////////////////////////////////////////
        // Encryption Constructor
        ////////////////////////////////////////////////////////////////////

        internal PdfEncryption
				(
				PdfDocument Document,
				string UserPassword,
				string OwnerPassword,
				Permission UserPermissions,
				EncryptionType EncryptionType
				) : base(Document)
			{
			// Notes:
			// The PDF File Writer library supports AES 128 encryption and standard 128 encryption.
			// The library does not strip leading or trailing white space. They are part of the password.
			// EncriptMetadata is assumed to be true (this libraray does not use metadata).
			// Embeded Files Only is assumed to be false (this library does not have embeded files).

			// remove all unused bits and add all bits that must be one
			Permissions = ((int) UserPermissions & (int) Permission.All) | PermissionBase;
			Dictionary.AddInteger("/P", Permissions);

			// convert user string password to byte array
			byte[] UserBinaryPassword = ProcessPassword(UserPassword);

			// convert owner string password to byte array
			if(string.IsNullOrEmpty(OwnerPassword))
				OwnerPassword = BitConverter.ToUInt64(PdfByteArrayMethods.RandomByteArray(8), 0).ToString();
			byte[] OwnerBinaryPassword = ProcessPassword(OwnerPassword);

			// calculate owner key for crypto dictionary
			byte[] OwnerKey = CreateOwnerKey(UserBinaryPassword, OwnerBinaryPassword);

			// create master key and user key
			CreateMasterKey(UserBinaryPassword, OwnerKey);
			byte[] UserKey = CreateUserKey();

			// build dictionary
			Dictionary.Add("/Filter", "/Standard");

			// encryption type
			this.EncryptionType = EncryptionType;
			if(EncryptionType == EncryptionType.Aes128)
				{
                Dictionary.Add("/Length", "128");
                Dictionary.Add("/O", PdfByteArrayMethods.ByteArrayToPdfHexString(OwnerKey));
                Dictionary.Add("/U", PdfByteArrayMethods.ByteArrayToPdfHexString(UserKey));
                Dictionary.Add("/R", "4");
				Dictionary.Add("/V", "4");
				Dictionary.Add("/StrF", "/StdCF");
				Dictionary.Add("/StmF", "/StdCF");
				Dictionary.Add("/CF", "<</StdCF<</Length 16/AuthEvent/DocOpen/CFM/AESV2>>>>");
				}
            else if (EncryptionType == EncryptionType.Aes256)
            {
                byte[] nextObjectKey;
                int nextObjectKeySize;

                int PERMS_MASK_1_FOR_REVISION_2 = unchecked((int)(0xffffffc0));
                int PERMS_MASK_1_FOR_REVISION_3_OR_GREATER = unchecked((int)(0xfffff0c0));
                int PERMS_MASK_2 = unchecked((int)(0xfffffffc));

                byte[] ownerPassword = Encoding.UTF8.GetBytes(OwnerPassword);
                byte[] userPassword = Encoding.UTF8.GetBytes(UserPassword);
                int permissions = Permissions;
                bool encryptMetadata = true;
                bool embeddedFilesOnly = false;

                ownerPassword = GenerateOwnerPasswordIfNullOrEmpty(ownerPassword);
                permissions |= PERMS_MASK_1_FOR_REVISION_3_OR_GREATER;
                permissions &= PERMS_MASK_2;
                //try
                //{
                    byte[] userKey;
                    byte[] ownerKey;
                    byte[] ueKey;
                    byte[] oeKey;
                    byte[] aes256Perms;
                    if (userPassword == null)
                    {
                        userPassword = new byte[0];
                    }
                    else
                    {
                        if (userPassword.Length > 127)
                        {
                            userPassword = ArraysCopyOf(userPassword, 127);
                        }
                    }
                    if (ownerPassword.Length > 127)
                    {
                        ownerPassword = ArraysCopyOf(ownerPassword, 127);
                    }
                    // first 8 bytes are validation salt; second 8 bytes are key salt
                    byte[] userValAndKeySalt = GetIV(16);
                    byte[] ownerValAndKeySalt = GetIV(16);
                    nextObjectKey = GetIV(32);
                    nextObjectKeySize = 32;
                    byte[] hash;
                    // Algorithm 8.1
                    hash = ComputeHash(userPassword, userValAndKeySalt, 0, 8);
                    userKey = ArraysCopyOf(hash, 48);
                    Array.Copy(userValAndKeySalt, 0, userKey, 32, 16);
                    // Algorithm 8.2
                    hash = ComputeHash(userPassword, userValAndKeySalt, 8, 8);
                    //AESCipherCBCnoPad ac = new AESCipherCBCnoPad(true, hash);
                    //ueKey = ac.ProcessBlock(nextObjectKey, 0, nextObjectKey.Length);
                    //Aes aes = Aes.Create();
                    //ueKey = nextObjectKey.AESEncrypt(hash, new byte[16], 256, CBCBlockSize, PaddingMode.None);
                    ueKey = nextObjectKey.AESEncrypt(hash, new byte[16], 256, CBCBlockSize, PaddingMode.None);
                    // Algorithm 9.1
                    hash = ComputeHash(ownerPassword, ownerValAndKeySalt, 0, 8, userKey);
                    ownerKey = ArraysCopyOf(hash, 48);
                    Array.Copy(ownerValAndKeySalt, 0, ownerKey, 32, 16);
                    // Algorithm 9.2
                    hash = ComputeHash(ownerPassword, ownerValAndKeySalt, 8, 8, userKey);
                    //ac = new AESCipherCBCnoPad(true, hash);
                    //oeKey = ac.ProcessBlock(nextObjectKey, 0, nextObjectKey.Length);
                    oeKey = nextObjectKey.AESEncrypt(hash, new byte[16], 256, CBCBlockSize, PaddingMode.None);
                    // Algorithm 10
                    byte[] permsp = GetIV(16);
                    permsp[0] = (byte)permissions;
                    permsp[1] = (byte)(permissions >> 8);
                    permsp[2] = (byte)(permissions >> 16);
                    permsp[3] = (byte)(permissions >> 24);
                    permsp[4] = (byte)(255);
                    permsp[5] = (byte)(255);
                    permsp[6] = (byte)(255);
                    permsp[7] = (byte)(255);
                    permsp[8] = encryptMetadata ? (byte)'T' : (byte)'F';
                    permsp[9] = (byte)'a';
                    permsp[10] = (byte)'d';
                    permsp[11] = (byte)'b';
                    //ac = new AESCipherCBCnoPad(true, nextObjectKey);
                    //aes256Perms = ac.ProcessBlock(permsp, 0, permsp.Length);
                    aes256Perms = permsp.AESEncrypt(nextObjectKey, new byte[16], 256, CBCBlockSize, PaddingMode.None);
                    //this.permissions = permissions;
                    //this.encryptMetadata = encryptMetadata;
                    //SetStandardHandlerDicEntries(/*encryptionDictionary, */userKey, ownerKey);
                    //SetAES256DicEntries(/*encryptionDictionary, */oeKey, ueKey, aes256Perms, encryptMetadata, embeddedFilesOnly);
                //}
                //catch (Exception ex)
                //{
                    //throw new PdfException(KernelExceptionMessageConstant.PDF_ENCRYPTION, ex);
                //}

                int vAes256 = 5;
                int rAes256 = 5;
                int rAes256Pdf2 = 6;

                Dictionary.Add("/Length", "256");
                Dictionary.Add("/O", PdfByteArrayMethods.ByteArrayToPdfHexString(ownerKey));
                Dictionary.Add("/U", PdfByteArrayMethods.ByteArrayToPdfHexString(userKey));
                Dictionary.Add("/OE", PdfByteArrayMethods.ByteArrayToPdfHexString(oeKey));
                Dictionary.Add("/UE", PdfByteArrayMethods.ByteArrayToPdfHexString(ueKey));
                Dictionary.Add("/R", (isPdf2 ? rAes256Pdf2 : rAes256).ToString());
                Dictionary.Add("/V", vAes256.ToString());
                if (!encryptMetadata)
                {
                    //encryptionDictionary.Put(PdfName.EncryptMetadata, PdfBoolean.FALSE);
                    Dictionary.Add("/EncryptMetadata", "false");
                }
                //Dictionary.Add("/CF", "<</StdCF<</Length 16/AuthEvent/DocOpen/CFM/AESV2>>>>");
                if (embeddedFilesOnly)
                {
                    Dictionary.Add("/EFF", "/StdCF");
                    Dictionary.Add("/StrF", "/Identity");
                    Dictionary.Add("/StmF", "/Identity");
                    Dictionary.Add("/CF", "<</StdCF<</Length 32/AuthEvent/EFOpen/CFM/AESV3>>>>");
                }
                else
                {
                    Dictionary.Add("/StrF", "/StdCF");
                    Dictionary.Add("/StmF", "/StdCF");
                    Dictionary.Add("/CF", "<</StdCF<</Length 32/AuthEvent/DocOpen/CFM/AESV3>>>>");
                }
                
            }
            else
				{
                Dictionary.Add("/Length", "128");
                Dictionary.Add("/O", PdfByteArrayMethods.ByteArrayToPdfHexString(OwnerKey));
                Dictionary.Add("/U", PdfByteArrayMethods.ByteArrayToPdfHexString(UserKey));
                Dictionary.Add("/R", "3");
				Dictionary.Add("/V", "2");
				}

			// encryption dictionary must be in file
			XRefType = XRefObjType.InFile;
			return;
			}

		////////////////////////////////////////////////////////////////////
		// Encrypt byte array
		////////////////////////////////////////////////////////////////////
		internal byte[] EncryptByteArray
				(
				int ObjectNumber,
				byte[] PlainText
				)
			{
			// create encryption key
			byte[] EncryptionKey = CreateEncryptionKey(ObjectNumber);
			byte[] CipherText;

			if(EncryptionType == EncryptionType.Aes128)
				{
				// generate new initialization vector IV 
				AES.GenerateIV();

				// create cipher text buffer including initialization vector
				int CipherTextLen = (PlainText.Length & 0x7ffffff0) + 16;
				CipherText = new byte[CipherTextLen + 16];
				Array.Copy(AES.IV, 0, CipherText, 0, 16);

				// set encryption key and key length
				AES.Key = EncryptionKey;

				// Create the streams used for encryption.
				MemoryStream OutputStream = new MemoryStream();
				CryptoStream CryptoStream = new CryptoStream(OutputStream, AES.CreateEncryptor(), CryptoStreamMode.Write);

				// write plain text byte array
				CryptoStream.Write(PlainText, 0, PlainText.Length);

				// encrypt plain text to cipher text
				CryptoStream.FlushFinalBlock();

				// get the result
				OutputStream.Seek(0, SeekOrigin.Begin);
				OutputStream.Read(CipherText, 16, CipherTextLen);

				// release resources
				CryptoStream.Clear();
				OutputStream.Close();
				}
            else if (EncryptionType == EncryptionType.Aes256)
            {
                // generate new initialization vector IV 
                AES.GenerateIV();

                // create cipher text buffer including initialization vector
                int CipherTextLen = (PlainText.Length & 0x7ffffff0) + 32;
                CipherText = new byte[CipherTextLen + 32];
                Array.Copy(AES.IV, 0, CipherText, 0, 16);

                // set encryption key and key length
                AES.Key = EncryptionKey;

                // Create the streams used for encryption.
                MemoryStream OutputStream = new MemoryStream();
                CryptoStream CryptoStream = new CryptoStream(OutputStream, AES.CreateEncryptor(), CryptoStreamMode.Write);

                // write plain text byte array
                CryptoStream.Write(PlainText, 0, PlainText.Length);

                // encrypt plain text to cipher text
                CryptoStream.FlushFinalBlock();

                // get the result
                OutputStream.Seek(0, SeekOrigin.Begin);
                OutputStream.Read(CipherText, 16, CipherTextLen);

                // release resources
                CryptoStream.Clear();
                OutputStream.Close();
            }
            else
				{
				CipherText = (byte[]) PlainText.Clone();
				EncryptRC4(EncryptionKey, CipherText);
				}

			// return result
			return CipherText;
			}

		////////////////////////////////////////////////////////////////////
		// Process Password
		////////////////////////////////////////////////////////////////////
		private static byte[] ProcessPassword
				(
				string StringPassword
				)
			{
			// no user password
			if(string.IsNullOrEmpty(StringPassword)) return (byte[]) PasswordPad.Clone();

			// convert password to byte array
			byte[] BinaryPassword = new byte[32];
			int IndexEnd = Math.Min(StringPassword.Length, 32);
			for(int Index = 0; Index < IndexEnd; Index++)
				{
				char PWChar = StringPassword[Index];
				if(PWChar > 255) throw new ApplicationException("Owner or user Password has invalid character (allowed 0-255)");
				BinaryPassword[Index] = (byte) PWChar;
				}

			// if user password is shorter than 32 bytes, add padding			
			if(IndexEnd < 32) Array.Copy(PasswordPad, 0, BinaryPassword, IndexEnd, 32 - IndexEnd);

			// return password
			return BinaryPassword;
			}

		////////////////////////////////////////////////////////////////////
		// Create owner key
		////////////////////////////////////////////////////////////////////
		private byte[] CreateOwnerKey
				(
				byte[] UserBinaryPassword,
				byte[] OwnerBinaryPassword
				)
			{
			// create hash array for owner password
			byte[] OwnerHash = MD5.ComputeHash(OwnerBinaryPassword);

			// loop 50 times creating hash of a hash
			for(int Index = 0; Index < 50; Index++) OwnerHash = MD5.ComputeHash(OwnerHash);

			byte[] OwnerKey = (byte[]) UserBinaryPassword.Clone();
			byte[] TempKey = new byte[16];
			for(int Index = 0; Index < 20; Index++)
				{
				for(int Tindex = 0; Tindex < 16; Tindex++) TempKey[Tindex] = (byte) (OwnerHash[Tindex] ^ Index);
				EncryptRC4(TempKey, OwnerKey);
				}

			// return encryption key
			return OwnerKey;
			}

		////////////////////////////////////////////////////////////////////
		// Create master key
		////////////////////////////////////////////////////////////////////
		private void CreateMasterKey
				(
				byte[] UserBinaryPassword,
				byte[] OwnerKey
				)
			{
			// input byte array for MD5 hash function
			byte[] HashInput = new byte[UserBinaryPassword.Length + OwnerKey.Length + 4 + Document.DocumentID.Length];
			int Ptr = 0;
			Array.Copy(UserBinaryPassword, 0, HashInput, Ptr, UserBinaryPassword.Length);
			Ptr += UserBinaryPassword.Length;
			Array.Copy(OwnerKey, 0, HashInput, Ptr, OwnerKey.Length);
			Ptr += OwnerKey.Length;
			HashInput[Ptr++] = (byte) Permissions;
			HashInput[Ptr++] = (byte) (Permissions >> 8);
			HashInput[Ptr++] = (byte) (Permissions >> 16);
			HashInput[Ptr++] = (byte) (Permissions >> 24);
			Array.Copy(Document.DocumentID, 0, HashInput, Ptr, Document.DocumentID.Length);
			MasterKey = MD5.ComputeHash(HashInput);

			// loop 50 times creating hash of a hash
			for(int Index = 0; Index < 50; Index++) MasterKey = MD5.ComputeHash(MasterKey);

			// exit
			return;
			}

		////////////////////////////////////////////////////////////////////
		// Create user key
		////////////////////////////////////////////////////////////////////
		private byte[] CreateUserKey()
			{
			// input byte array for MD5 hash function
			byte[] HashInput = new byte[PasswordPad.Length + Document.DocumentID.Length];
			Array.Copy(PasswordPad, 0, HashInput, 0, PasswordPad.Length);
			Array.Copy(Document.DocumentID, 0, HashInput, PasswordPad.Length, Document.DocumentID.Length);
			byte[] UserKey = MD5.ComputeHash(HashInput);
			byte[] TempKey = new byte[16];

			for(int Index = 0; Index < 20; Index++)
				{
				for(int Tindex = 0; Tindex < 16; Tindex++) TempKey[Tindex] = (byte) (MasterKey[Tindex] ^ Index);
				EncryptRC4(TempKey, UserKey);
				}
			Array.Resize<byte>(ref UserKey, 32);
			return UserKey;
			}

		////////////////////////////////////////////////////////////////////
		// Create encryption key
		////////////////////////////////////////////////////////////////////
		private byte[] CreateEncryptionKey
				(
				int ObjectNumber
				)
			{
            //byte[] HashInput = new byte[MasterKey.Length + 5 + (EncryptionType == EncryptionType.Aes128 ? Salt.Length : 0)];
            byte[] HashInput = new byte[MasterKey.Length + 5 + (EncryptionType == EncryptionType.Aes128 || EncryptionType == EncryptionType.Aes256 ? Salt.Length : 0)];
            int Ptr = 0;
			Array.Copy(MasterKey, 0, HashInput, Ptr, MasterKey.Length);
			Ptr += MasterKey.Length;
			HashInput[Ptr++] = (byte) ObjectNumber;
			HashInput[Ptr++] = (byte) (ObjectNumber >> 8);
			HashInput[Ptr++] = (byte) (ObjectNumber >> 16);
			HashInput[Ptr++] = 0;   // Generation is always zero for this library
			HashInput[Ptr++] = 0;   // Generation is always zero for this library
                                    //if(EncryptionType == EncryptionType.Aes128) Array.Copy(Salt, 0, HashInput, Ptr, Salt.Length);
            if (EncryptionType == EncryptionType.Aes128 || EncryptionType == EncryptionType.Aes256) Array.Copy(Salt, 0, HashInput, Ptr, Salt.Length);
            byte[] EncryptionKey = MD5.ComputeHash(HashInput);
			if(EncryptionKey.Length > 16) Array.Resize<byte>(ref EncryptionKey, 16);
			return EncryptionKey;
			}

		////////////////////////////////////////////////////////////////////
		// RC4 Encryption
		////////////////////////////////////////////////////////////////////
		private static void EncryptRC4
				(
				byte[] Key,
				byte[] Data
				)
			{
			byte[] State = new byte[256];
			for(int Index = 0; Index < 256; Index++) State[Index] = (byte) Index;

			int Index1 = 0;
			int Index2 = 0;
			for(int Index = 0; Index < 256; Index++)
				{
				Index2 = (Key[Index1] + State[Index] + Index2) & 255;
				byte tmp = State[Index];
				State[Index] = State[Index2];
				State[Index2] = tmp;
				Index1 = (Index1 + 1) % Key.Length;
				}

			int x = 0;
			int y = 0;
			for(int Index = 0; Index < Data.Length; Index++)
				{
				x = (x + 1) & 255;
				y = (State[x] + y) & 255;
				byte tmp = State[x];
				State[x] = State[y];
				State[y] = tmp;
				Data[Index] = (byte) (Data[Index] ^ State[(State[x] + State[y]) & 255]);
				}
			return;
			}

		////////////////////////////////////////////////////////////////////
		/// <summary>
		/// Dispose unmanaged resources
		/// </summary>
		////////////////////////////////////////////////////////////////////
		public void Dispose()
			{
			if(AES != null)
				{
				AES.Clear();
				// NOTE: AES.Dispose() is valid for .NET 4.0 and later.
				// In other words visual studio 2010 and later.
				// If you compile this source with older versions of VS
				// remove this call at your risk.
				AES.Dispose();
				AES = null;
				}

			if(MD5 != null)
				{
				MD5.Clear();
				MD5 = null;
				}
			return;
			}
        ///////// aes256 encrypt start
        public T[] ArraysCopyOf<T>(T[] original, int newLength)
        {
            T[] copy = new T[newLength];
            System.Array.Copy(original, 0, copy, 0, Math.Min(original.Length, newLength));
            return copy;
        }
        public long GetTimeBasedSeed()
        {
            return DateTime.Now.Ticks + Environment.TickCount;
        }
        public long GetFreeMemory()
        {
            return GC.GetTotalMemory(false);
        }
		public Encoding ISO_8859_1()
		{
			return (Encoding.GetEncoding("ISO-8859-1"));
		}
        public byte[] GenerateNewDocumentId()
        {
            long seq = GetTimeBasedSeed();
            //IIDigest sha512;
            SHA512 sHA512 = SHA512.Create();
			//try
            {
                //sha512 = iText.Bouncycastleconnector.BouncyCastleFactoryCreator.GetFactory().CreateIDigest("SHA-512");
            }
            //catch (Exception e)
            {
                //throw new PdfException(KernelExceptionMessageConstant.PDF_ENCRYPTION, e);
            }
            long time = GetTimeBasedSeed();
            long mem = GetFreeMemory();
            String s = time + "+" + mem + "+" + (seq++);
			//return sha512.Digest(s.GetBytes(iText.Commons.Utils.EncodingUtil.ISO_8859_1));
			return (sHA512.ComputeHash(ISO_8859_1().GetBytes(s)));
        }
        public byte[] GetIV(int len)
        {
            ARCFOUREncryption arcfour;
            arcfour = new ARCFOUREncryption();
            long time = GetTimeBasedSeed();
            long mem = GetFreeMemory();
            String s = time + "+" + mem;
            arcfour.PrepareARCFOURKey(ISO_8859_1().GetBytes(s));

            byte[] b = new byte[len];
            lock (arcfour)
            {
                arcfour.EncryptARCFOUR(b);
            }
            return b;
        }
        private byte[] GenerateOwnerPasswordIfNullOrEmpty(byte[] ownerPassword)
        {
            if (ownerPassword == null || ownerPassword.Length == 0)
            {
				//MD5.ComputeHash()
				//ownerPassword = md5.Digest(PdfEncryption.GenerateNewDocumentId());
				MD5 md5 = MD5.Create();
				ownerPassword = md5.ComputeHash(GenerateNewDocumentId());
            }
            return ownerPassword;
        }
        public byte[] GetChunk(byte[] source, int sourceOffset, int length)
        {
            byte[] result = new byte[0];
            if (source.Length > 0)
            {
                result = new byte[length];
                Buffer.BlockCopy(source, sourceOffset, result, 0, length);
            }
            return (result);
        }
        private byte[] ComputeHash(byte[] password, byte[] salt, int saltOffset, int saltLen)
        {
            return ComputeHash(password, salt, saltOffset, saltLen, null);
        }
        private byte[] ComputeHash(byte[] password, byte[] salt, int saltOffset, int saltLen, byte[]? userKey)
        {
            SHA256 sha256Crypto = SHA256.Create();
            byte[] sha256Hash = new byte[0];
            sha256Crypto.Initialize();

            if (userKey != null)
            {
                sha256Crypto.TransformBlock(password, 0, password.Length, null, 0);
                sha256Crypto.TransformBlock(salt, saltOffset, saltLen, null, 0);
                sha256Crypto.TransformFinalBlock(userKey, 0, userKey.Length);
            }
            else
            {
                sha256Crypto.TransformBlock(password, 0, password.Length, null, 0);
                sha256Crypto.TransformFinalBlock(salt, saltOffset, saltLen);
            }
            string saltStr = BitConverter.ToString(salt);
            if (userKey != null) { string userKeyStr = BitConverter.ToString(userKey); } // for testing purposes

            byte[] k = sha256Crypto.Hash != null ? sha256Crypto.Hash : new byte[0];
            if (isPdf2)
            {
                // See 7.6.4.3.3 "Algorithm 2.B"
                //IDigest mdSha384 = DigestUtilities.GetDigest("SHA-384");
                SHA384 sha384Crypto = SHA384.Create();

                //IDigest mdSha512 = DigestUtilities.GetDigest("SHA-512");
                SHA512 sha512Crypto = SHA512.Create();

                int userKeyLen = userKey != null ? userKey.Length : 0;
                int passAndUserKeyLen = password.Length + userKeyLen;
                // k1 repetition length
                int k1RepLen;
                int roundNum = 0;
                while (true)
                {
                    // a)
                    k1RepLen = passAndUserKeyLen + k.Length;
                    byte[] k1 = new byte[k1RepLen * 64];
                    Array.Copy(password, 0, k1, 0, password.Length);
                    Array.Copy(k, 0, k1, password.Length, k.Length);
                    if (userKey != null)
                    {
                        Array.Copy(userKey, 0, k1, password.Length + k.Length, userKeyLen);
                    }
                    for (int i = 1; i < 64; ++i)
                    {
                        Array.Copy(k1, 0, k1, k1RepLen * i, k1RepLen);
                    }
                    // b)
                    //AESCipherCBCnoPad cipher = new AESCipherCBCnoPad(
                    //    true, JavaUtil.ArraysCopyOf(k, 16), JavaUtil.ArraysCopyOfRange
                    //    (k, 16, 32));
                    //byte[] e = cipher.ProcessBlock(k1, 0, k1.Length);
                    byte[] e = k1.AESEncrypt(GetChunk(k, 0, 16), GetChunk(k, 16, 32 - 16), 256, CBCBlockSize, PaddingMode.None);
                    string eStr = BitConverter.ToString(e);
                    // c)
                    //IDigest md = null;
                    //string md = "";
                    //BigInteger i_1 = new BigInteger(1, JavaUtil.ArraysCopyOf(e, 16));
                    //Org.BouncyCastle.Math.BigInteger i_1_test = new(1, e.GetChunk(0, 16));
                    System.Numerics.BigInteger i_1 = new System.Numerics.BigInteger(GetChunk(e, 0, 16), true, true);
                    //int remainder_test = i_1_test.Remainder(Org.BouncyCastle.Math.BigInteger.ValueOf(3)).IntValue;
                    int remainder = (int)BigInteger.Remainder(i_1, new BigInteger(3));

                    // d)
                    switch (remainder)
                    {
                        case 0:
                            {
                                k = sha256Crypto.ComputeHash(e);
                                break;
                            }

                        case 1:
                            {
                                k = sha384Crypto.ComputeHash(e);
                                break;
                            }

                        case 2:
                            {
                                k = sha512Crypto.ComputeHash(e);
                                break;
                            }
                    }

                    ++roundNum;
                    if (roundNum > 63)
                    {
                        // e)
                        // interpreting last byte as unsigned integer
                        int condVal = e[e.Length - 1] & 0xFF;
                        if (condVal <= roundNum - 32)
                        {
                            break;
                        }
                    }
                }
                //k = k.Length == 32 ? k : JavaUtil.ArraysCopyOf(k, 32);
                k = k.Length == 32 ? k : GetChunk(k, 0, 32);
            }
            return k;
        }
        private void SetStandardHandlerDicEntries(PdfDictionary encryptionDictionary, byte[] userKey
            , byte[] ownerKey)
        {
            //encryptionDictionary.Put(PdfName.Filter, PdfName.Standard);
            //encryptionDictionary.Put(PdfName.O, new PdfLiteral(StreamUtil.CreateEscapedString(ownerKey)));
            //encryptionDictionary.Put(PdfName.U, new PdfLiteral(StreamUtil.CreateEscapedString(userKey)));
            //encryptionDictionary.Put(PdfName.P, new PdfNumber(permissions));

        }
        private void InitKeyAndFillDictionary(/*PdfDictionary encryptionDictionary, */byte[] userPassword, byte[] ownerPassword
            , int permissions, bool encryptMetadata, bool embeddedFilesOnly)
        {
			byte[] nextObjectKey;
			int nextObjectKeySize;

            int PERMS_MASK_1_FOR_REVISION_2 = unchecked((int)(0xffffffc0));
			int PERMS_MASK_1_FOR_REVISION_3_OR_GREATER = unchecked((int)(0xfffff0c0));
			int PERMS_MASK_2 = unchecked((int)(0xfffffffc));

			ownerPassword = GenerateOwnerPasswordIfNullOrEmpty(ownerPassword);
            permissions |= PERMS_MASK_1_FOR_REVISION_3_OR_GREATER;
            permissions &= PERMS_MASK_2;
            try
            {
                byte[] userKey;
                byte[] ownerKey;
                byte[] ueKey;
                byte[] oeKey;
                byte[] aes256Perms;
                if (userPassword == null)
                {
                    userPassword = new byte[0];
                }
                else
                {
                    if (userPassword.Length > 127)
                    {
                        userPassword = ArraysCopyOf(userPassword, 127);
                    }
                }
                if (ownerPassword.Length > 127)
                {
                    ownerPassword = ArraysCopyOf(ownerPassword, 127);
                }
                // first 8 bytes are validation salt; second 8 bytes are key salt
                byte[] userValAndKeySalt = GetIV(16);
                byte[] ownerValAndKeySalt = GetIV(16);
                nextObjectKey = GetIV(32);
                nextObjectKeySize = 32;
                byte[] hash;
                // Algorithm 8.1
                hash = ComputeHash(userPassword, userValAndKeySalt, 0, 8);
                userKey = ArraysCopyOf(hash, 48);
                Array.Copy(userValAndKeySalt, 0, userKey, 32, 16);
                // Algorithm 8.2
                hash = ComputeHash(userPassword, userValAndKeySalt, 8, 8);
                //AESCipherCBCnoPad ac = new AESCipherCBCnoPad(true, hash);
                //ueKey = ac.ProcessBlock(nextObjectKey, 0, nextObjectKey.Length);
                Aes aes = Aes.Create();
                ueKey = nextObjectKey.AESEncrypt(hash, new byte[nextObjectKeySize], 256, CBCBlockSize, PaddingMode.None);
                // Algorithm 9.1
                hash = ComputeHash(ownerPassword, ownerValAndKeySalt, 0, 8, userKey);
                ownerKey = ArraysCopyOf(hash, 48);
                Array.Copy(ownerValAndKeySalt, 0, ownerKey, 32, 16);
                // Algorithm 9.2
                hash = ComputeHash(ownerPassword, ownerValAndKeySalt, 8, 8, userKey);
                //ac = new AESCipherCBCnoPad(true, hash);
                //oeKey = ac.ProcessBlock(nextObjectKey, 0, nextObjectKey.Length);
                oeKey = nextObjectKey.AESEncrypt(hash, new byte[nextObjectKeySize], 256, CBCBlockSize, PaddingMode.None);
                // Algorithm 10
                byte[] permsp = GetIV(16);
                permsp[0] = (byte)permissions;
                permsp[1] = (byte)(permissions >> 8);
                permsp[2] = (byte)(permissions >> 16);
                permsp[3] = (byte)(permissions >> 24);
                permsp[4] = (byte)(255);
                permsp[5] = (byte)(255);
                permsp[6] = (byte)(255);
                permsp[7] = (byte)(255);
                permsp[8] = encryptMetadata ? (byte)'T' : (byte)'F';
                permsp[9] = (byte)'a';
                permsp[10] = (byte)'d';
                permsp[11] = (byte)'b';
                //ac = new AESCipherCBCnoPad(true, nextObjectKey);
                //aes256Perms = ac.ProcessBlock(permsp, 0, permsp.Length);
                aes256Perms = permsp.AESEncrypt(nextObjectKey, new byte[permsp.Length], 256, CBCBlockSize, PaddingMode.None);
                //this.permissions = permissions;
                //this.encryptMetadata = encryptMetadata;
                //SetStandardHandlerDicEntries(/*encryptionDictionary, */userKey, ownerKey);
                //SetAES256DicEntries(/*encryptionDictionary, */oeKey, ueKey, aes256Perms, encryptMetadata, embeddedFilesOnly);
            }
            catch (Exception ex)
            {
                //throw new PdfException(KernelExceptionMessageConstant.PDF_ENCRYPTION, ex);
            }
        }

        private void SetAES256DicEntries(/*PdfDictionary encryptionDictionary, */byte[] oeKey, byte[] ueKey, byte[] aes256Perms
            , bool encryptMetadata, bool embeddedFilesOnly)
        {
            int vAes256 = 5;
            int rAes256 = 5;
            int rAes256Pdf2 = 6;
            //encryptionDictionary.Put(PdfName.OE, new PdfLiteral(StreamUtil.CreateEscapedString(oeKey)));
            //encryptionDictionary.Put(PdfName.UE, new PdfLiteral(StreamUtil.CreateEscapedString(ueKey)));
            //encryptionDictionary.Put(PdfName.Perms, new PdfLiteral(StreamUtil.CreateEscapedString(aes256Perms)));
            //encryptionDictionary.Put(PdfName.R, new PdfNumber(isPdf2 ? rAes256Pdf2 : rAes256));
            //encryptionDictionary.Put(PdfName.V, new PdfNumber(vAes256));
            //PdfDictionary stdcf = new PdfDictionary();
            //stdcf.Put(PdfName.Length, new PdfNumber(32));
            if (!encryptMetadata)
            {
                //encryptionDictionary.Put(PdfName.EncryptMetadata, PdfBoolean.FALSE);
            }
            if (embeddedFilesOnly)
            {
                //stdcf.Put(PdfName.AuthEvent, PdfName.EFOpen);
                //encryptionDictionary.Put(PdfName.EFF, PdfName.StdCF);
                //encryptionDictionary.Put(PdfName.StrF, PdfName.Identity);
                //encryptionDictionary.Put(PdfName.StmF, PdfName.Identity);
            }
            else
            {
                //stdcf.Put(PdfName.AuthEvent, PdfName.DocOpen);
                //encryptionDictionary.Put(PdfName.StrF, PdfName.StdCF);
                //encryptionDictionary.Put(PdfName.StmF, PdfName.StdCF);
            }
            //stdcf.Put(PdfName.CFM, PdfName.AESV3);
            //PdfDictionary cf = new PdfDictionary();
            //cf.Put(PdfName.StdCF, stdcf);
            //encryptionDictionary.Put(PdfName.CF, cf);
        }
        ///////// aes256 encrypt end
    }
    ////// aes256 encrypt subclass start
    public class ARCFOUREncryption
    {
        private byte[] state = new byte[256];

        private int x;

        private int y;

        /// <summary>Creates a new instance of ARCFOUREncryption</summary>
        public ARCFOUREncryption()
        {
        }

        public virtual void PrepareARCFOURKey(byte[] key)
        {
            PrepareARCFOURKey(key, 0, key.Length);
        }

        public virtual void PrepareARCFOURKey(byte[] key, int off, int len)
        {
            int index1 = 0;
            int index2 = 0;
            for (int k = 0; k < 256; ++k)
            {
                state[k] = (byte)k;
            }
            x = 0;
            y = 0;
            byte tmp;
            for (int k = 0; k < 256; ++k)
            {
                index2 = (key[index1 + off] + state[k] + index2) & 255;
                tmp = state[k];
                state[k] = state[index2];
                state[index2] = tmp;
                index1 = (index1 + 1) % len;
            }
        }

        public virtual void EncryptARCFOUR(byte[] dataIn, int off, int len, byte[] dataOut, int offOut)
        {
            int length = len + off;
            byte tmp;
            for (int k = off; k < length; ++k)
            {
                x = (x + 1) & 255;
                y = (state[x] + y) & 255;
                tmp = state[x];
                state[x] = state[y];
                state[y] = tmp;
                dataOut[k - off + offOut] = (byte)(dataIn[k] ^ state[(state[x] + state[y]) & 255]);
            }
        }

        public virtual void EncryptARCFOUR(byte[] data, int off, int len)
        {
            EncryptARCFOUR(data, off, len, data, off);
        }

        public virtual void EncryptARCFOUR(byte[] dataIn, byte[] dataOut)
        {
            EncryptARCFOUR(dataIn, 0, dataIn.Length, dataOut, 0);
        }

        public virtual void EncryptARCFOUR(byte[] data)
        {
            EncryptARCFOUR(data, 0, data.Length, data, 0);
        }
    }
    ////// aes256 encrypt subclass end

    ////// aes256 encryption helper start
    public static class AesHelperExtensions
    {
        /*
        var key = new byte[16] { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
        var iv = new byte[16] { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
        var input = new byte[16] { 0x1E, 0xA0, 0x35, 0x3A, 0x7D, 0x29, 0x47, 0xD8, 0xBB, 0xC6, 0xAD, 0x6F, 0xB5, 0x2F, 0xCA, 0x84 };

        var crypto = new AesCryptographyService();

        var encrypted = crypto.Encrypt(input, key, iv);
        var str = BitConverter.ToString(encrypted).Replace("-", "");
        Console.WriteLine(str);
        */

        public static byte[] AESEncrypt(this byte[] data, byte[] key, byte[] iv,
            int keySize = 256, int blockSize = 128, PaddingMode paddingMode = PaddingMode.PKCS7)
        {
            using (var aes = Aes.Create())
            {
                aes.KeySize = keySize;
                aes.BlockSize = blockSize;
                aes.Padding = paddingMode;

                aes.Key = key;
                aes.IV = iv;

                using (var encryptor = aes.CreateEncryptor(aes.Key, aes.IV))
                {
                    return PerformCryptography(data, encryptor);
                }
            }
        }

        public static byte[] AESDecrypt(this byte[] data, byte[] key, byte[] iv,
            int keySize = 256, int blockSize = 128, PaddingMode paddingMode = PaddingMode.PKCS7)
        {
            using (var aes = Aes.Create())
            {
                aes.KeySize = keySize;
                aes.BlockSize = blockSize;
                aes.Padding = paddingMode;

                aes.Key = key;
                if (iv != null) { aes.IV = iv; }

                using (var decryptor = aes.CreateDecryptor(aes.Key, aes.IV))
                {
                    return PerformCryptography(data, decryptor);
                }
            }
        }

        private static byte[] PerformCryptography(byte[] data, ICryptoTransform cryptoTransform)
        {
            using (var ms = new MemoryStream())
            using (var cryptoStream = new CryptoStream(ms, cryptoTransform, CryptoStreamMode.Write))
            {
                cryptoStream.Write(data, 0, data.Length);
                cryptoStream.FlushFinalBlock();

                return ms.ToArray();
            }
        }
    }
    ////// aes256 encryption helper end
}
