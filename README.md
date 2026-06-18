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
The `reverse.dfy` utility reads a source file and writes a new destination file with the lines strictly reversed. 
The core challenge of this utility was eliminating the unverified `assume {:axiom} buffer.Length < 0x80000000` prior to writing to the `FileStream`. The `FileStream.Write` interface inherently requires an `int32` size, meaning we had to mathematically prove the buffer size would not exceed this boundary.

**Design & Proof Chain:**
To achieve memory safety verification without `assume` statements, we designed a robust mathematical chain mapping the abstract sequences of lines back to the concrete buffer bytes:
1. **Mathematical Models:** We created two functions:
   - `linesSize(lines)`: Computes the sum of all raw content bytes across the array of lines.
   - `outputSize(lines)`: Computes the total exact bytes required for the final buffer, accounting for the `\n` separators (`linesSize(lines) + max(|lines|-1, 0)`).
2. **Bounds Tracking:** We defined invariants in `SplitByNewline` guaranteeing that `outputSize(lines) <= |buffer|`. Since the initial `buffer.Length` is derived directly from `FileLength` (which yields an `int32` and thus `< 0x80000000`), Dafny proves `outputSize` must also be `< 0x80000000`.
3. **Reversal Preservation:** We implemented recursive lemmas demonstrating that `ReverseLines` perfectly preserves the `outputSize` property.
4. **Final Assembly:** The `LinesToBytes` loop invariants prove that the resulting flattened `byte` array has exactly `outputSize` length. Because `outputSize < 0x80000000`, the final `buffer.Length as int32` cast is completely verified and mathematically safe.

### 2. Grep Naive & KMP Utilities (`grep-naive/grep.dfy` and `grep-kmp/grep.dfy`)
Both naive and KMP string-matching utilities were implemented to search a source file for a given word.

**Design Decisions:**
- **KMP Optimization:** The `grep-kmp` implementation utilizes the Knuth-Morris-Pratt algorithm, operating in `O(N + M)` time. It correctly builds the `lps` (Longest Prefix Suffix) array in `O(M)` time to bypass redundant character checking during the `O(N)` search phase.
- **Bonus Requirement - UNIX-Style Printing:** We went beyond the base requirement (printing `YES: <position>`) and implemented the **bonus challenge** for both algorithms: printing the exact matched lines from the file and highlighting the matched word in red using ANSI escape sequences.
- **Architectural Separation:** To maintain the strict time complexity of the KMP algorithm while achieving the advanced line-printing logic, the implementation is explicitly decoupled into two phases:
  1. **Search Phase:** The algorithm purely searches and returns a sequence of matched indices.
  2. **Display Phase:** The `PrintMatchingLines` method processes the file byte array in a single O(N) pass. It does not perform string matching; instead, it checks the pre-computed KMP indices. When it hits a valid index, it uses the provided `word.Length` to toggle ANSI color flags, guaranteeing that the formatting pass does not degrade the overarching O(N) search complexity.