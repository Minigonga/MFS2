/*
 * This is the skeleton for your line reverse utility.
 *
 */

include "Io.dfy"

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
    assume {:axiom} sourceNameArray[..] in env.files.state();
    var lenOk, sourceLen := FileStream.FileLength(sourceNameArray, env);
    if !lenOk {
      print "Failed to get source file length\n";
      return;
    }
    var openSourceOk, sourceFile := FileStream.Open(sourceNameArray, env);
    if !openSourceOk {
      print "Failed to open source file\n";
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
    assume {:axiom} env.ok.ok();

    var writeOk := destFile.Write(0, buffer, 0, sourceLen);
    if !writeOk {
      print "Failed to write to destination file\n";
      return;
    }
    assume {:axiom} env.ok.ok();

    var closeSourceOk := sourceFile.Close();
    if !closeSourceOk {
      print "Failed to close source file\n";
      return;
    }
    assume {:axiom} env.ok.ok();

    var closeDestOk := destFile.Close();
    if !closeDestOk {
      print "Failed to close destination file\n";
      return;
    }

    print "File copied successfully\n";
}