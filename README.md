# MFS Project 2

## Group Elements

- up202204943 Gonçalo Pinto
- up202205143 José Granja
- up202205000 Manuel Mo

## How to run

### Reverse

Create a "SourceFile" in the reverse directory with the text to reverse the lines.
```bash
cd reverse
dafny reverse.dfy IoNative.cs
./reverse SourceFile DestFile
```

### Grep Naive

Create a file in the grep-naive directory with text to search through.
```bash
cd grep-naive
dafny grep.dfy IoNative.cs
./grep <word> <file>
```

### Grep KMP

Create a file in the grep-kmp directory with text to search through.
```bash
cd grep-kmp
dafny grep.dfy IoNative.cs
./grep <word> <file>
```

## Accomplished Work
Describe the work you have accomplished so far, and any work you have left to do. Describe also any extras you have implemented beyond the requirements.