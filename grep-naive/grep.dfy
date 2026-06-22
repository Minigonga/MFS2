/*  
 * Verified Grep Utility - Naive String Matching Algorithm
 * Finds all occurrences of a word/pattern in a file
 */

include "Io.dfy"

predicate wordMatchesAtPosition(posText: int, txt: array<byte>, posWord: int, word: array<char>, len: int)
requires 0 <= posText
requires 0 <= posWord
requires 0 <= len
requires posText + len <= txt.Length
requires posWord + len <= word.Length
reads txt, word
{
    len == 0 || (txt[posText + len - 1] as char == word[posWord + len - 1] && wordMatchesAtPosition(posText, txt, posWord, word, len - 1))
}

// Helper method to find all positions where pattern occurs in file content
method FindPatternInFile(word: array<char>, fileContent: array<byte>) returns (positions: seq<int>)
requires word.Length > 0
ensures forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= fileContent.Length - word.Length
ensures forall k :: 0 <= k < |positions| ==> wordMatchesAtPosition(positions[k], fileContent, 0, word, word.Length)
{
    var contentLen := fileContent.Length;

    positions := [];

    if contentLen < word.Length {
        return;
    }

    var pos := 0;
    var matches := true;
    while pos <= contentLen - word.Length
    invariant 0 <= pos <= contentLen 
    invariant forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= contentLen - word.Length
    invariant forall k :: 0 <= k < |positions| ==> wordMatchesAtPosition(positions[k], fileContent, 0, word, word.Length)
    decreases contentLen - pos
    {
        matches := true;
        var i := 0;

        while i < word.Length && matches
        invariant 0 <= i <= word.Length
        invariant matches ==> wordMatchesAtPosition(pos, fileContent, 0, word, i)
        {
            if fileContent[pos + i] as char != word[i] {
                matches := false;
            }
            i := i + 1;
        }

        if matches {
            positions := positions + [pos];
            pos := pos + word.Length;
        } else{
            pos := pos + 1;
        }

    }
}

// Prints each file line that contains a KMP match, highlighting matched words in red.
// positions must be sorted ascending (guaranteed by the KMP search order) and each
// position must satisfy positions[k] + word.Length <= fileContent.Length.
method PrintSearchResult(word: array<char>, fileContent: array<byte>, positions: seq<int>)
requires word.Length > 0
requires forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= fileContent.Length - word.Length
requires forall k :: 0 <= k < |positions| ==> wordMatchesAtPosition(positions[k], fileContent, 0, word, word.Length)
{
    if |positions| == 0 { return; }

    var esc := [27 as char, '['];
    var red := ['3','1','m'];
    var reset := ['0','m'];
    var contentLen := fileContent.Length;
    var pos := 0;
    var matchIdx := 0;
    var line: seq<char> := [];
    var wordOnLine := false;

    while pos < contentLen
        invariant 0 <= pos <= contentLen
        invariant 0 <= matchIdx <= |positions|
    {
        // End of line
        if fileContent[pos] == 10 {
            // Print the line because the pattern exists on it
            if wordOnLine {
                print line, "\n";
            }
            // Reset the line
            line := [];
            wordOnLine := false;
            pos := pos + 1;
            continue;
        }

        // If this byte is the start of the next KMP match, highlight the word
        if matchIdx < |positions| && pos == positions[matchIdx] {
            var startPos := pos;
            assert startPos + word.Length <= fileContent.Length;
            wordOnLine := true;
            line := line + esc + red; // Used to put the output as red
            while pos < startPos + word.Length
                invariant startPos <= pos <= startPos + word.Length
                invariant pos <= fileContent.Length
            {
                line := line + [fileContent[pos] as char];
                pos := pos + 1;
            }
            line := line + esc + reset; // Used to reset the colour of the output
            matchIdx := matchIdx + 1;
        } else {
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
        print "Error: The file doesn't exist\n";
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
    var positions := FindPatternInFile(word, buffer);

    PrintSearchResult(word, buffer, positions);
    
    // Close the file
    var closeOk := file.Close();
    if !closeOk {
        print "Error: Failed to close file\n";
        return;
    }

}
