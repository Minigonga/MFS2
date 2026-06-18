# MFS Project 2

## Group Elements

- up202204943 Gonçalo Pinto
- up202205143 José Granja
- up202205000 Manuel Mo

## How to run

### Reverse

Create a source file in the reverse directory with the text to reverse the lines.
If you have the destination file already created you should delete it before running the script.

```bash
cd reverse
dafny reverse.dfy IoNative.cs
./reverse <SourceFile> <DestFile>
```

### Grep Naive

Create a file in the grep-naive directory with text to search through.

```bash
cd grep-naive
dafny grep.dfy IoNative.cs
./grep <pattern> <file>    # If the pattern has spaces it needs to be between "".
```

### Grep KMP

Create a file in the grep-kmp directory with text to search through.

```bash
cd grep-kmp
dafny grep.dfy IoNative.cs
./grep <pattern> <file>    # If the pattern has spaces it needs to be between "".
```

## What it does?

### 1. Reverse Utility (`reverse/reverse.dfy`)

The `reverse.dfy` utility reads a source file and writes to a new destination file (that can't exist before execution) with the lines strictly reversed. Empty lines are perfectly preserved, regardless of whether they appear at the beginning, middle, or end of the file.

To accomplish this, the utility relies on three core methods: `SplitByNewline`, `ReverseLines` and `LinesToBytes`. The first method parses the file into a list of every line, the second reverses that list (effectively reversing the lines of the file), and the third concatenates the lines back into a flat byte buffer. The critical constraint across all three methods is guaranteeing that the final buffer size remains strictly smaller than `0x80000000` (the 2 GB limit of an `int32`). If we didn't have these strict `ensures` clauses, the compiler would need to assume that the buffer was smaller than `0x80000000` with `assume {:axiom} buffer.Length < 0x80000000` to safely execute the final write operation.

**Execution Flow (Main):**

1. Validate command-line arguments, expecting exactly 3: the executable (./reverse), the source file name and the destination file name.
2. Check if the destination file already exists, if it does, stops execution.
3. Check if the source file exists, if it doesn't, stops execution.
4. Open both files and get the source file's length.
5. Read the entire source file into a byte buffer.
6. Parse the buffer into individual lines using `SplitByNewline`.
7. Reverse the order of the lines using `ReverseLines`.
8. Flatten the lines back into a byte buffer using `LinesToBytes`.
9. Write the resulting buffer to the destination file.
10. Close both files and print a success message.

**Implementation Details:**

The core challenge of this utility was implementing the low-level byte manipulation and file I/O operations while satisfying Dafny's strict mathematical verifier, specifically removing the need for an unverified size assumption before calling `FileStream.Write`.

- **Parsing and Splitting (`SplitByNewline`):** We manually iterate through the file's raw byte array, isolating sequences of bytes delimited by the newline character (`\n` / ASCII 10) into a sequence of sequences (`seq<seq<byte>>`).
- **Reversal (`ReverseLines`):** The parsed lines are iterated backwards and appended to a new sequence, efficiently reversing their order while maintaining the contents of each individual line.
- **Serialization (`LinesToBytes`):** The reversed sequence of lines is flattened back into a single 1D `array<byte>`, with the `\n` separator precisely re-inserted between lines.

**Formal Verification & Memory Safety:**

To mathematically prove the absence of out-of-bounds memory accesses and ensure loop termination, we developed a robust proof chain:

1. **Mathematical Models (Ghost Functions):** We created two ghost functions: 
   - `linesSize(lines)`: Recursively computes the sum of all raw content bytes inside a `seq<seq<byte>>`.
   - `outputSize(lines)`: Computes the total bytes required to serialize the lines, including the `\n` separators (`linesSize(lines) + max(|lines|-1, 0)`).
2. **Inductive Proof Lemmas:** Dafny cannot automatically deduce how the total size of a 2D sequence (`seq<seq<byte>>`) changes when a new sequence is appended to it. To solve this, we explicitly proved two mathematical lemmas:
   - `LinesSizeAppend(lines, line)`: Uses structural induction to formally prove that appending a `line` to the `lines` sequence increases the `linesSize` by exactly `|line|`.
   - `OutputSizeAppend(lines, line)`: Builds upon the previous lemma to prove that appending a new line increases the total `outputSize` by exactly `|line| + 1` (accounting for the additional `\n` separator). 
3. **Bounds Tracking (`SplitByNewline`):** We defined loop invariants in `SplitByNewline` linking the number of processed bytes `i` to the abstract `outputSize(lines)`. By calling the `OutputSizeAppend` lemma every time a line is finalized, the invariant proves that `outputSize(lines) <= |buffer|`. Since the initial `buffer.Length` is derived directly from `FileLength` (which yields an `int32` and thus `< 0x80000000`), Dafny securely proves `outputSize` must also strictly be `< 0x80000000`.
4. **Preserving Bounds (`ReverseLines`):** The invariants in `ReverseLines` (aided by `LinesSizeAppend`) mathematically guarantee that `outputSize(reversed) == outputSize(lines)`, ensuring that the reversed lines also fit in memory.
5. **Final Assembly (`LinesToBytes`):** The `LinesToBytes` method reconstructs the 1D array, with its loop invariants tracking the exact number of bytes written. When the loop finishes, the invariant guarantees that the resulting flattened byte array has exactly `outputSize` length. This guarantees that the final `buffer.Length as int32` cast is mathematically safe, allowing the code to be 100% verified without relying on unsafe `assume {:axiom}` statements.

### 2. Grep Naive & KMP Utilities (`grep-naive/grep.dfy` and `grep-kmp/grep.dfy`)

The `grep.dfy` utility receives a pattern and a file, reads the file and prints all the lines from the file that have the word in it, the word is also highlighted with a different colour (red). In cases like the pattern is atat and there is a section with atatat the text will appear with only the first atat with the red colour <span style="color:red;">atat</span>at, like this because the method searches for a word and doesn't use any part of that word to match another word. In a case where the section was for example atatatat the output would bet <span style="color:red;">atatatat</span> because the second atat doesn't use any part of the first match. For the pattern it is not needed to have "" but if the pattern has spaces it is.

**Execution Flow (Main):**
1. First check the number of arguments, it should be 3, the ./reverse, the name of the source file and the name of the destination file.
2. Check if the destination file already exists, if it exists it stops because it shouldn't exist.
3. Check if the source file exists, it only continues if it does.
4. Open both files and get the length of the source file.
5. Read the source file.
6. Reverse the lines.
7. Write on the destination file.
8. Close both files.

### 2.1 Grep Naive (`grep-naive/grep.dfy`)

This grep implementation uses the **naive string-matching algorithm**, which runs in **O(n * m)** time in the worst case, where n is the size of the file and m is the size of the pattern. The algorithm scans the file character by character and, at each position, attempts to match the entire pattern against the following characters in the text.

As its name suggests, this is a straightforward approach because it does not use any information from previous comparisons. Whenever a mismatch occurs, the algorithm simply moves to the next position in the file and starts comparing the pattern from the beginning again. In the worst case, this can require up to m comparisons for each of the n positions in the file, resulting in the time complexity we talked before.

To keep the implementation simple and avoid additional memory usage, lines are printed as soon as they are fully processed and a match has been found, rather than storing all matching lines and printing them later.

### 2.2 Grep KMP (`grep-kmp/grep.dfy`)

This grep implementation uses the **Knuth-Morris-Pratt (KMP)** algorithm, which runs in **O(n + m)** time, where n is the size of the file and m is the size of the pattern. Unlike the naive implementation, which may repeatedly compare future characters after each mismatch, KMP processes each character of the file at most once. When a mismatch occurs, it does not restart the comparison from the next file position. Instead, it uses information about the pattern itself to determine where the next comparison should begin.

To achieve this, KMP first builds an **LPS (Longest Proper Prefix which is also a Suffix)** array (implemented in our code as `constructLps`). The LPS array stores, for each position in the pattern, the length of the longest prefix that is also a suffix of the substring ending at that position. This allows the algorithm to skip unnecessary comparisons after a mismatch.

For example, for the pattern **"ababc"**, the LPS array is **[0, 0, 1, 2, 0]**. At index 2 ('a'), the value is 1 because the prefix "a" is also a suffix of "aba". At index 3 ('b'), the value is 2 because "ab" is both a prefix and a suffix of "abab". These values help the algorithm continue matching from the longest valid prefix instead of starting over, improving efficiency compared to the naive approach.

In this implementation we decided to get the initial position where the pattern appears and then print the lines that has the pattern there.