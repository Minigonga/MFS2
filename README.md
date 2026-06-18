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

## Accomplished Work

This project has been fully implemented, successfully fulfilling all functional requirements, verification obligations, and bonus challenges.

### 1. Reverse Utility (`reverse/reverse.dfy`)
The `reverse.dfy` utility was built entirely from scratch to read a source file, parse its contents, reverse the order of the lines, and write the result to a new destination file. The core challenge of this utility was implementing the low-level byte manipulation and file I/O operations while satisfying Dafny's strict mathematical verifier.

**Implementation Details:**
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
Both naive and KMP string-matching utilities were implemented to search a source file for a given word.

**Design Decisions:**
- **KMP Optimization:** The `grep-kmp` implementation utilizes the Knuth-Morris-Pratt algorithm, operating in `O(N + M)` time. It correctly builds the `lps` (Longest Prefix Suffix) array in `O(M)` time to bypass redundant character checking during the `O(N)` search phase.
- **Bonus Requirement - UNIX-Style Printing:** We went beyond the base requirement (printing `YES: <position>`) and implemented the **bonus challenge** for both algorithms: printing the exact matched lines from the file and highlighting the matched word in red using ANSI escape sequences.
- **Architectural Separation:** To maintain the strict time complexity of the KMP algorithm while achieving the advanced line-printing logic, the implementation is explicitly decoupled into two phases:
  1. **Search Phase:** The algorithm purely searches and returns a sequence of matched indices.
  2. **Display Phase:** The `PrintMatchingLines` method processes the file byte array in a single O(N) pass. It does not perform string matching; instead, it checks the pre-computed KMP indices. When it hits a valid index, it uses the provided `word.Length` to toggle ANSI color flags, guaranteeing that the formatting pass does not degrade the overarching O(N) search complexity.