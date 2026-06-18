/*
 * Verified Line Reverse Utility
 * Reads a source file and writes a destination file with all lines in reverse order.
 * The memory-safety proof chain guarantees buffer lengths never exceed int32 (0x80000000).
 * (See README.md for a detailed proof explanation).
 */

include "Io.dfy"

// Total content bytes across all lines (no newline separators).
function linesSize(lines: seq<seq<byte>>): nat
{
  if |lines| == 0 then 0
  else |lines[0]| + linesSize(lines[1..])
}

// Bytes produced by LinesToBytes: content + (|lines|-1) separator newlines.
function outputSize(lines: seq<seq<byte>>): nat
{
  if |lines| == 0 then 0
  else linesSize(lines) + |lines| - 1
}

// Appending a line increases linesSize by exactly |line|.
lemma LinesSizeAppend(lines: seq<seq<byte>>, line: seq<byte>)
  ensures linesSize(lines + [line]) == linesSize(lines) + |line|
{
  if |lines| == 0 {
    // base case: linesSize([] + [line]) == |line|
  } else {
    // inductive step
    assert (lines + [line])[1..] == lines[1..] + [line];
    LinesSizeAppend(lines[1..], line);
  }
}

// outputSize grows when we append a new line (accounting for separator).
lemma OutputSizeAppend(lines: seq<seq<byte>>, line: seq<byte>)
  requires |lines| >= 0
  ensures outputSize(lines + [line]) == outputSize(lines) + |line| + (if |lines| > 0 then 1 else 0)
{
  LinesSizeAppend(lines, line);
  if |lines| == 0 {
    assert lines + [line] == [line];
    assert outputSize([line]) == |line|;
    assert outputSize(lines) == 0;
  } else {
    // inductive step: outputSize grows by |line| + 1 (for the newline separator)
  }
}

// Split buffer on '\n' (ASCII 10).
// Invariant links the processed bytes to outputSize, proving it stays within bounds.
method SplitByNewline(buffer: seq<byte>) returns (lines: seq<seq<byte>>)
  requires |buffer| < 0x80000000
  ensures outputSize(lines) < 0x80000000
{
  lines := [];
  var currentLine: seq<byte> := [];
  var i := 0;

  while i < |buffer|
    invariant 0 <= i <= |buffer|
    // Invariant: bytes accounted for = content in completed lines
    //            + separating newlines between them
    //            + content in current in-progress line
    invariant outputSize(lines) + |currentLine| + (if |lines| > 0 then 1 else 0) <= i + (if |lines| == 0 then 0 else 0)
    // Simplified: let's use the concrete count
    invariant linesSize(lines) + |currentLine| + |lines| == i
  {
    if buffer[i] == 10 {  // '\n'
      OutputSizeAppend(lines, currentLine);
      LinesSizeAppend(lines, currentLine);
      lines := lines + [currentLine];
      currentLine := [];
    } else {
      currentLine := currentLine + [buffer[i]];
    }
    i := i + 1;
  }

  // Commit trailing line if non-empty.
  if |currentLine| > 0 {
    OutputSizeAppend(lines, currentLine);
    LinesSizeAppend(lines, currentLine);
    lines := lines + [currentLine];
  }
}

lemma LinesSizeReverse(lines: seq<seq<byte>>, i: int)
  requires 0 <= i <= |lines|
  ensures linesSize(lines) == linesSize(lines[..i]) + linesSize(lines[i..])
{
  if i == 0 {
    assert lines[..0] == [];
  } else {
    assert lines[..i] == [lines[0]] + lines[1..i];
    LinesSizeReverse(lines[1..], i - 1);
    assert lines[1..][..i-1] == lines[1..i];
    assert lines[1..][i-1..] == lines[i..];
  }
}

// Reverse the order of lines; preserves linesSize and outputSize.
method ReverseLines(lines: seq<seq<byte>>) returns (reversed: seq<seq<byte>>)
  requires outputSize(lines) < 0x80000000
  ensures |reversed| == |lines|
  ensures linesSize(reversed) == linesSize(lines)
  ensures outputSize(reversed) == outputSize(lines)
  ensures outputSize(reversed) < 0x80000000
{
  reversed := [];
  var i := |lines| - 1;
  while i >= 0
    invariant -1 <= i <= |lines| - 1
    invariant |reversed| == |lines| - 1 - i
    invariant linesSize(reversed) == linesSize(lines[i+1..])
  {
    LinesSizeAppend(reversed, lines[i]);
    reversed := reversed + [lines[i]];
    i := i - 1;
  }
  // After loop: linesSize(reversed) == linesSize(lines[0..]) == linesSize(lines)
  assert lines[0..] == lines;
}

// Convert lines back to a flat buffer with '\n' separators.
// Output length == outputSize(lines), proven by the loop invariant on |result|.
// Since outputSize(lines) < 0x80000000, buffer.Length < 0x80000000 — no assume needed.
method LinesToBytes(lines: seq<seq<byte>>) returns (buffer: array<byte>)
  requires outputSize(lines) < 0x80000000
  ensures buffer.Length == outputSize(lines)
  ensures buffer.Length < 0x80000000
{
  var result: seq<byte> := [];
  var i := 0;
  while i < |lines|
    invariant 0 <= i <= |lines|
    // Tracks bytes written (content + separators)
    invariant |result| == (
      if i == 0 then 0
      else if i < |lines| then linesSize(lines[..i]) + i
      else linesSize(lines[..i]) + i - 1
    )
  {
    LinesSizeAppend(lines[..i], lines[i]);
    assert lines[..i] + [lines[i]] == lines[..i+1];
    result := result + lines[i];
    if i < |lines| - 1 {
      result := result + [10];  // 10 is \n
    }
    i := i + 1;
  }

  // After loop: i == |lines|.
  // Invariant gives: |result| == linesSize(lines[..|lines|]) + |lines| - 1
  assert lines[..|lines|] == lines;
  assert |result| == outputSize(lines);

  buffer := new byte[|result|];
  var j := 0;
  while j < |result|
    invariant 0 <= j <= |result|
    invariant buffer[..j] == result[..j]
  {
    buffer[j] := result[j];
    j := j + 1;
  }
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  modifies env.ok
  modifies env.files
{
    var numArgs := HostConstants.NumCommandLineArgs(env);
    if numArgs != 3 {
      print "Usage: reverse <source> <destination>\n";
      return;
    }
    var sourceNameArray := HostConstants.GetCommandLineArg(1, env);
    var destNameArray := HostConstants.GetCommandLineArg(2, env);
    var destExists := FileStream.FileExists(destNameArray, env);
    if destExists {
      print "Destination file already exists\n";
      return;
    }
    var sourceExists := FileStream.FileExists(sourceNameArray, env);
    if !sourceExists {
      print "Source file doesn't exist\n";
      return;
    }
    var openSourceOk, sourceFile := FileStream.Open(sourceNameArray, env);
    if !openSourceOk {
      print "Failed to open source file\n";
      return;
    }
    var lenOk, sourceLen := FileStream.FileLength(sourceNameArray, env);
    if !lenOk {
      print "Failed to get source file length\n";
      return;
    }
    var openDestOk, destFile := FileStream.Open(destNameArray, env);
    if !openDestOk {
      print "Failed to open destination file\n";
      return;
    }

    var buffer := new byte[sourceLen];
    var readOk := sourceFile.Read(0, buffer, 0, sourceLen);
    if !readOk {
      print "Failed to read source file\n";
      return;
    }

    // Parse into lines
    var lines := SplitByNewline(buffer[..]);

    // Reverse lines
    var reversedLines := ReverseLines(lines);

    // Convert back to bytes
    buffer := LinesToBytes(reversedLines);

    var writeOk := destFile.Write(0, buffer, 0, buffer.Length as int32);

    if !writeOk {
      print "Failed to write to destination file\n";
      return;
    }

    var closeSourceOk := sourceFile.Close();
    if !closeSourceOk {
      print "Failed to close source file\n";
      return;
    }

    var closeDestOk := destFile.Close();
    if !closeDestOk {
      print "Failed to close destination file\n";
      return;
    }

    print "File reversed and copied successfully\n";
}