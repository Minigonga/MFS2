/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"

method SplitByNewline(buffer: seq<byte>) returns (lines: seq<seq<byte>>)
{
  var result: seq<seq<byte>> := [];
  var currentLine: seq<byte> := [];
  var i := 0;
  while i < |buffer|
  {
    if buffer[i] == 10 {  // 10 is ASCII for '\n'
      result := result + [currentLine];
      currentLine := [];
    } else {
      currentLine := currentLine + [buffer[i]];
    }
    i := i + 1;
  }
  if |currentLine| > 0 {
    result := result + [currentLine];
  }
  return result;
}

method ReverseLines(lines: seq<seq<byte>>) returns (reversed: seq<seq<byte>>)
{
  var result: seq<seq<byte>> := [];
  var i := |lines| - 1;
  while i >= 0
  {
    result := result + [lines[i]];
    i := i - 1;
  }
  return result;
}

method LinesToBytes(lines: seq<seq<byte>>) returns (buffer: array<byte>)
{
  var result: seq<byte> := [];
  var i := 0;
  while i < |lines|
  {
    result := result + lines[i];
    if i < |lines| - 1 {
      result := result + [10];  // 10 is '\n'
    }
    i := i + 1;
  }
  buffer := new byte[|result|];
  var j := 0;
  while j < |result|
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
    if sourceExists {
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

    assume {:axiom} buffer.Length < 0x80000000; // TODO: ensures para tirar este assume
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

    print "File copied successfully\n";
}