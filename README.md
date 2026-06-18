# MFS Project 2

## Group Elements

- up202204943 Gonçalo Pinto
- up202205143 José Granja
- up202205000 Manuel Mo

## How to run

### Reverse

Create a "SourceFile" in the reverse directory with the text to reverse the lines.

#### Without Makefile
```bash
cd reverse
dafny reverse.dfy IoNative.cs
./reverse SourceFile DestFile
```

#### With Makefile
```bash
cd reverse
make compile
./reverse SourceFile DestFile
```

### Grep Naive

Create a file in the grep-naive directory with text to search through.

#### Without Makefile
```bash
cd grep-naive
dafny grep.dfy IoNative.cs
./grep <word> <file>
```

#### With Makefile
```bash
cd grep-naive
make compile
./grep <word> <file>
```

### Grep KMP

Create a file in the grep-kmp directory with text to search through.

#### Without Makefile
```bash
cd grep-kmp
dafny grep.dfy IoNative.cs
./grep <word> <file>
```

#### With Makefile
```bash
cd grep-kmp
make compile
./grep <word> <file>
```

### 1. Reverse Utility (`reverse/reverse.dfy`)

The `reverse.dfy` utility reads a source file and writes in a new destination file (that can't exist before running the reverse) with the lines strictly reversed without removing empty lines either in the begining, in the middle or in the end of the file.

To reverse the lines we created three methods, `SplitByNewline`, `ReverseLines` and `LinesToBytes`. The first creates a list with every line of the file, the second reverses the lines and in the third all the lines are concatenated again in the buffer to be called on the `Write` that is done after the three methods. The main part that we had to ensure on the three methods was that the size of the buffer was smaller than 0x80000000 that was the size of int32. If we didn't had any type of ensures on the methods we would need to assume that the buffer was smaller then 0x80000000 with `assume {:axiom} buffer.Length < 0x80000000`.

**Main**
1. First check the number of arguments, it should be 3, the ./reverse, the name of the source file and the name of the destination file.
2. Check if the destination file already exists, if it exists it stops because it shouldn't exist.
3. Check if the source file exists, it only continues if it does.
4. Open both files and get the length of the source file.
5. Read the source file.
6. Reverse the lines.
7. Write on the destination file.
8. Close both files.

??**Implementation Details:**
- **File I/O Management:** The utility utilizes the `HostEnvironment` and `FileStream` APIs to safely check file existence, retrieve file lengths, and handle the reading/writing of byte buffers, ensuring all system interactions are correctly tracked in Dafny's state (`env.ok`, `env.files`).
- **Parsing and Splitting (`SplitByNewline`):** We manually iterate through the file's raw byte array, isolating sequences of bytes delimited by the newline character (`\n` / ASCII 10) into a sequence of sequences (`seq<seq<byte>>`).
- **Reversal (`ReverseLines`):** The parsed lines are iterated backwards and appended to a new sequence, efficiently reversing their order while maintaining the contents of each individual line.
- **Serialization (`LinesToBytes`):** The reversed sequence of lines is flattened back into a single 1D `array<byte>`, with the `\n` separator precisely re-inserted between lines.

**Formal Verification & Memory Safety:**
To mathematically prove the absence of out-of-bounds memory accesses and ensure loop termination, we developed a robust proof chain:
1. **Mathematical Models:** We created two ghost functions: `linesSize(lines)` (total content bytes) and `outputSize(lines)` (total bytes including `\n` separators). 
2. **Bounds Tracking:** We defined complex loop invariants in `SplitByNewline` to prove that `outputSize(lines) <= |buffer|`. Since the initial `buffer.Length` is derived directly from `FileLength` (which yields an `int32` and thus `< 0x80000000`), Dafny proves `outputSize` must also strictly be `< 0x80000000`.
3. **Reversal Preservation:** Recursive lemmas were implemented to demonstrate that `ReverseLines` perfectly preserves the `outputSize` property.
4. **Final Assembly:** The `LinesToBytes` loop invariants prove that the resulting flattened byte array has exactly `outputSize` length. This guaranteed that the final `buffer.Length as int32` cast is mathematically safe, allowing the code to be 100% verified without relying on unsafe `assume {:axiom}` statements.

### 2. Grep Naive & KMP Utilities (`grep-naive/grep.dfy` and `grep-kmp/grep.dfy`)

The `grep.dfy` utility receives a pattern and a file, reads the file and prints all the lines from the file that have the word in it, the word is also highlighted with a different colour (red). In cases like the pattern is atat and there is a section with atatat the text will appear with only the first atat with the red colour <span style="color:red;">atat</span>at, like this because the method searches for a word and doesn't use any part of that word to match another word. In a case where the section was for example atatatat the output would bet <span style="color:red;">atatatat</span> because the second atat doesn't use any part of the first match.

**Main**
1. First check the number of arguments, it should be 3, the ./reverse, the name of the source file and the name of the destination file.
2. Check if the destination file already exists, if it exists it stops because it shouldn't exist.
3. Check if the source file exists, it only continues if it does.
4. Open both files and get the length of the source file.
5. Read the source file.
6. Reverse the lines.
7. Write on the destination file.
8. Close both files.

??Both naive and KMP string-matching utilities were implemented to search a source file for a given word.

**Design Decisions:**
- **KMP Optimization:** The `grep-kmp` implementation utilizes the Knuth-Morris-Pratt algorithm, operating in `O(N + M)` time. It correctly builds the `lps` (Longest Prefix Suffix) array in `O(M)` time to bypass redundant character checking during the `O(N)` search phase.
- **Bonus Requirement - UNIX-Style Printing:** We went beyond the base requirement (printing `YES: <position>`) and implemented the **bonus challenge** for both algorithms: printing the exact matched lines from the file and highlighting the matched word in red using ANSI escape sequences.
- **Architectural Separation:** To maintain the strict time complexity of the KMP algorithm while achieving the advanced line-printing logic, the implementation is explicitly decoupled into two phases:
  1. **Search Phase:** The algorithm purely searches and returns a sequence of matched indices.
  2. **Display Phase:** The `PrintMatchingLines` method processes the file byte array in a single O(N) pass. It does not perform string matching; instead, it checks the pre-computed KMP indices. When it hits a valid index, it uses the provided `word.Length` to toggle ANSI color flags, guaranteeing that the formatting pass does not degrade the overarching O(N) search complexity.

### 2. Grep Naive (`grep-naive/grep.dfy`)



### 3. Grep KMP (`grep-kmp/grep.dfy`)

Both naive and KMP string-matching utilities were implemented to search a source file for a given word.

**Design Decisions:**
- **KMP Optimization:** The `grep-kmp` implementation utilizes the Knuth-Morris-Pratt algorithm, operating in `O(N + M)` time. It correctly builds the `lps` (Longest Prefix Suffix) array in `O(M)` time to bypass redundant character checking during the `O(N)` search phase.
- **Bonus Requirement - UNIX-Style Printing:** We went beyond the base requirement (printing `YES: <position>`) and implemented the **bonus challenge** for both algorithms: printing the exact matched lines from the file and highlighting the matched word in red using ANSI escape sequences.
- **Architectural Separation:** To maintain the strict time complexity of the KMP algorithm while achieving the advanced line-printing logic, the implementation is explicitly decoupled into two phases:
  1. **Search Phase:** The algorithm purely searches and returns a sequence of matched indices.
  2. **Display Phase:** The `PrintMatchingLines` method processes the file byte array in a single O(N) pass. It does not perform string matching; instead, it checks the pre-computed KMP indices. When it hits a valid index, it uses the provided `word.Length` to toggle ANSI color flags, guaranteeing that the formatting pass does not degrade the overarching O(N) search complexity.