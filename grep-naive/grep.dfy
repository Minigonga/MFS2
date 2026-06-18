/*  
 * Verified Grep Utility - Naive String Matching Algorithm
 * Finds all occurrences of a word/pattern in a file
 */

include "Io.dfy"

// Helper method to find all positions where pattern occurs in file content
method FindPatternInFile(word: array<char>, fileContent: array<byte>)
    requires word.Length > 0
{
    var contentLen := fileContent.Length;
    if (contentLen < word.Length){
        return;
    }
    var pos := 0;
    var esc := [27 as char, '['];
    var red := ['3','1','m'];
    var reset := ['0','m'];
    var line: seq<char> := [];
    var wordOnLine := false;
    var position := 0;
    var matches := true;
    var i := 0;

    while pos < contentLen
    invariant 0 <= pos <= contentLen + word.Length
    {
        // End of line: flush the current line and reset state
        if fileContent[pos] == 10 {
            if wordOnLine {
                print line, "\n";
            }
            line := [];
            wordOnLine := false;
            pos := pos + 1;
            continue;
        }

        if pos < contentLen - word.Length + 1 {
            matches := true;
            i := 0;
            // Check for a match starting at pos
            while i < word.Length && matches
            invariant 0 <= i <= word.Length
            {
                if fileContent[pos + i] as char != word[i] {
                    matches := false;
                }
                i := i + 1;
            }
        } else{
            matches := false;
        }

        if matches {
            position := pos;
            wordOnLine := true;
            line := line + esc + red;
                while pos < position + word.Length
                invariant 0 <= pos <= word.Length + position
                {   
                    line := line + [fileContent[pos] as char];
                    pos := pos + 1;
                }
            line := line + esc + reset;
        } else{
            line := line + [fileContent[pos] as char];
            pos := pos + 1;
        }

    }

    // Handle last line if file doesn't end with '\n'
    if |line| > 0 && wordOnLine {
        print line, "\n";
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
        print "Usage: grep <word> <file>\n";
        return;
    }
    
    // Get command-line arguments
    var word := HostConstants.GetCommandLineArg(1, env);
    var fileName := HostConstants.GetCommandLineArg(2, env);
    
    if word.Length == 0 {
        print "Error: word cannot be empty\n";
        return;
    }
    
    // Check if file exists
    var fileExists := FileStream.FileExists(fileName, env);
    if !fileExists {
        print "The file doesn't exist\n";
        return;
    }
    
    // Open the file
    var openOk, file := FileStream.Open(fileName, env);
    if !openOk {
        print "Error: Failed to open file\n";
        return;
    }
    // Get file length
    var lenOk, fileLen := FileStream.FileLength(fileName, env);
    if !lenOk {
        print "Error: Failed to get file length\n";
        return;
    }

    // Read entire file into buffer
    var buffer := new byte[fileLen];
    var readOk := file.Read(0, buffer, 0, fileLen);
    
    if !readOk {
        print "Error: Failed to read file\n";
        return;
    }
    
    // Find all positions where the pattern occurs
    FindPatternInFile(word, buffer);

    // Close the file
    var closeOk := file.Close();
    if !closeOk {
        print "Error: Failed to close file\n";
        return;
    }

}
