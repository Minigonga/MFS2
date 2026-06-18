/*  
 * Verified Grep Utility - Naive String Matching Algorithm
 * Finds the first occurrence of a word/pattern in a file
 */

include "Io.dfy"

// function CharToLower(c: char): char
// {
//     if 'A' <= c <= 'Z' then
//         ((c as int - 'A' as int + 'a' as int) as char)
//     else
//         c
// }

// function CharToLowerWithByte(b: byte): byte
// {
//     if 65 <= b <= 90 then
//         ((b as int - 65 + 97) as byte)
//     else
//         b
// }

// Helper method to convert a char array to lowercase
// method ConvertToLower(text: array<char>) returns (lower: array<char>)
//     requires text.Length > 0
//     ensures fresh(lower)
//     ensures lower.Length == text.Length
//     ensures forall i :: 0 <= i < lower.Length ==> lower[i] == CharToLower(text[i])
// {
//     lower := new char[text.Length];
//     var i := 0;
//     while i < text.Length
//         invariant 0 <= i <= text.Length
//         invariant forall j :: 0 <= j < i ==> lower[j] == CharToLower(text[j])
//     {
//         lower[i] := CharToLower(text[i]);
//         i := i + 1;
//     }
// }

// Helper method to find all positions where pattern occurs in file content
method FindPatternInFile(word: array<char>, fileContent: array<byte>) returns (positions: seq<int>)
    requires word.Length > 0
    ensures forall i :: 0 <= i < |positions| ==> 0 <= positions[i] < fileContent.Length
{
    var contentLen := fileContent.Length;
    var pos := 0;
    positions := [];
    while pos + word.Length <= contentLen
        invariant 0 <= pos <= contentLen
        invariant forall i :: 0 <= i < |positions| ==> 0 <= positions[i] < contentLen
    {
        var matches := true;
        var i := 0;
        while i < word.Length && matches
            invariant 0 <= i <= word.Length
        {
            if fileContent[pos + i] as char != word[i] {
                matches := false;
            }
            i := i + 1;
        }
        
        if matches {
            positions := positions + [pos];
        }
        
        pos := pos + 1;             // TODO: Acho que é preciso verificar new lines e coisas assim para posições de palavras
    }
    
}

// Helper function to generate output based on found positions
method PrintSearchResult(positions: seq<int>)
    requires forall i :: 0 <= i < |positions| ==> positions[i] >= 0
{
    if |positions| == 0 {
        print "NO\n";
    } else {
        print "YES: ";
        var i := 0;
        while i < |positions|
            invariant 0 <= i <= |positions|
        {
            if i > 0 {
                print ", ";
            }
            print positions[i];
            i := i + 1;
        }
        print "\n";
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
        print "NO\n";
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

    // Output result (YES: all positions or NO)
    PrintSearchResult(positions);

    // Close the file
    var closeOk := file.Close();
    if !closeOk {
        print "Error: Failed to close file\n";
        return;
    }

}
