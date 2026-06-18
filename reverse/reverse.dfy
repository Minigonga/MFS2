/*
 * Verified Line Reverse Utility
 * Reads a source file and writes a destination file with all lines in reverse order.
 * The memory-safety proof chain guarantees buffer lengths never exceed int32 (0x80000000).
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

// Appending a new line increases the outputSize by |line| + 1 (accounting for '\n').
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

// Splits the raw byte buffer into individual lines using the newline character ('\n') as a separator.
// The loop invariants formally prove the processed bytes mathematically map to the outputSize bounds.
method SplitByNewline(buffer: seq<byte>) returns (lines: seq<seq<byte>>)
  requires |buffer| < 0x80000000
  ensures outputSize(lines) < 0x80000000
{
  lines := [];
  var currentLine: seq<byte> := [];
  var i := 0;

  while i < |buffer|
    invariant 0 <= i <= |buffer|
    // content in completed lines + separating newlines between them + content in current in-progress line
    invariant outputSize(lines) + |currentLine| + (if |lines| > 0 then 1 else 0) <= i + (if |lines| == 0 then 0 else 0)
    invariant linesSize(lines) + |currentLine| + |lines| == i
  {
    if buffer[i] == 10 {  // '\n'
      OutputSizeAppend(lines, currentLine);
      LinesSizeAppend(lines, currentLine);
      // Append the completed line to our list
      lines := lines + [currentLine];
      // Reset the current line buffer for the next line
      currentLine := [];
    } else {
      // Append the character to the current in-progress line
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

// Reverses the sequence of lines, formally proving that the overall sizes (linesSize and outputSize) are preserved.
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
    // Append the line from the end of the original sequence to reverse the order
    reversed := reversed + [lines[i]];
    // Move backwards through the original sequence
    i := i - 1;
  }
  // After loop: linesSize(reversed) == linesSize(lines[0..]) == linesSize(lines)
  assert lines[0..] == lines;
}

// Convert lines back to a flat buffer with '\n' separators.
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
    
    // Append the actual line content to our flat sequence
    result := result + lines[i];
    
    // If this is not the final line, append a newline separator
    if i < |lines| - 1 {
      result := result + [10];  // 10 is '\n'
    }
    // Move to the next line
    i := i + 1;
  }

  assert lines[..|lines|] == lines;
  assert |result| == outputSize(lines);

  buffer := new byte[|result|];
  var j := 0;
  while j < |result|
    invariant 0 <= j <= |result|
    invariant buffer[..j] == result[..j]
  {
    // Copy the byte from our sequence into the final fixed-size array
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

    // Check correct number of arguments
    if numArgs != 3 {
      print "Usage: reverse <source> <destination>\n";
      return;
    }

    // Get command-line arguments
    var sourceNameArray := HostConstants.GetCommandLineArg(1, env);
    var destNameArray := HostConstants.GetCommandLineArg(2, env);

    // Check if source file exists, if it exists it continues
    var sourceExists := FileStream.FileExists(sourceNameArray, env);
    if !sourceExists {
      print "Error: Source file doesn't exist\n";
      return;
    }

    // Check if destination file exists, if it does it does not continue
    var destExists := FileStream.FileExists(destNameArray, env);
    if destExists {
      print "Error: Destination file already exists\n";
      return;
    }

    // Open the source file
    var openSourceOk, sourceFile := FileStream.Open(sourceNameArray, env);
    if !openSourceOk {
      print "Error: Failed to open source file\n";
      return;
    }

    // Get source file length
    var lenOk, sourceLen := FileStream.FileLength(sourceNameArray, env);
    if !lenOk {
      print "Error: Failed to get source file length\n";
      return;
    }

    // Open the destination file
    var openDestOk, destFile := FileStream.Open(destNameArray, env);
    if !openDestOk {
      print "Error: Failed to open destination file\n";
      return;
    }

    // Read entire file into buffer
    var buffer := new byte[sourceLen];
    var readOk := sourceFile.Read(0, buffer, 0, sourceLen);
    if !readOk {
      print "Error: Failed to read source file\n";
      return;
    }

    // Parse into lines
    var lines := SplitByNewline(buffer[..]);

    // Reverse lines
    var reversedLines := ReverseLines(lines);

    // Convert back to bytes
    buffer := LinesToBytes(reversedLines);

    // Write the destination file
    var writeOk := destFile.Write(0, buffer, 0, buffer.Length as int32);

    if !writeOk {
      print "Error: Failed to write to destination file\n";
      return;
    }

    // Close the source file
    var closeSourceOk := sourceFile.Close();
    if !closeSourceOk {
      print "Error: Failed to close source file\n";
      return;
    }

    // Close the destination file
    var closeDestOk := destFile.Close();
    if !closeDestOk {
      print "Error: Failed to close destination file\n";
      return;
    }

    print "File reversed and copied successfully\n";
}