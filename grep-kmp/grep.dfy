/*  
 * Verified Grep Utility - Knuth-Morris-Pratt Algorithm
 * Finds all occurrences of a word/pattern in a file
 */

include "Io.dfy"

// Builds the LPS (Longest Proper Prefix which is also a Suffix) table used by KMP.
// For each position i, lps[i] stores the length of the longest prefix of the pattern
// that is also a suffix ending at position i. This allows KMP to skip unnecessary
// comparisons after a mismatch instead of restarting from the beginning.
method constructLps(word: array<char>) returns (lps: array<int>)
requires word.Length > 0
ensures lps.Length == word.Length
ensures lps[0] == 0
ensures forall k :: 0 <= k < lps.Length ==> 0 <= lps[k] <= k
{
    lps := new int[word.Length];
    var len := 0;
    lps[0] := 0;
    var i := 1;
  
    while i < word.Length
    invariant 1 <= i <= word.Length
    invariant 0 <= len < i
    invariant lps[0] == 0
    invariant forall k :: 1 <= k < i ==> 0 <= lps[k] <= k
    decreases word.Length - i, len
    {
        // Current characters match:
        // extend the current prefix-suffix length.
        if word[i] == word[len] {
            len := len + 1;
            lps[i] := len;
            i := i + 1;
        }
        else {
            // Mismatch after some matches:
            // fall back to the previous valid prefix length.
            if len != 0 {
                len := lps[len - 1];
            }
            // No valid prefix before.
            else {
                lps[i] := 0;
                i := i + 1;
            }
        }
    }
}

// Performs KMP pattern matching on the file content.
// Returns all starting positions where the pattern appears.
// The algorithm uses the LPS table to avoid rechecking characters
// that have already been matched.
method search(word: array<char>, txt: array<byte>) returns (positions: seq<int>)
    requires word.Length > 0
    ensures forall i :: 0 <= i < |positions| ==> 0 <= positions[i] <= txt.Length - word.Length
{
    // Precompute information used to skip comparisons.
    var lps := constructLps(word);

    var n := txt.Length;
    var m := word.Length;
    positions := [];
    // Impossible to find a match if the pattern is longer than the text.
    if (txt.Length < word.Length){
      return;
    }

    var i := 0;
    var j := 0;
    var pos := 0;

    while i < n
        invariant 0 <= i <= n
        invariant 0 <= j <= m
        invariant i - j >= 0
        invariant forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= n - m
        decreases n - i, j
    {
        // Characters match: continue advancing in both text and pattern.
        if j < m && txt[i] as char == word[j] {
            i := i + 1;
            j := j + 1;

            // Entire pattern matched.
            if j == m {
                positions := positions + [i-j];
                // In a implementation for example in geeks for geeks to get all patterns even if they overlap other patterns
                // they use j := lps[j-i]; but we don't want any type of overlaps.
                j := 0;
            }
        }
        else {
            // Mismatch after partial match:
            // use the LPS table to determine the next pattern position.
            if j != 0 {
                j := lps[j - 1];
            }
            // No partial match exists, move to next text character.
            else {
                i := i + 1;
            }
        }
    }
}

// Prints each file line that contains a KMP match, highlighting matched words in red.
// positions must be sorted ascending (guaranteed by the KMP search order) and each
// position must satisfy positions[k] + word.Length <= fileContent.Length.
method PrintSearchResult(word: array<char>, fileContent: array<byte>, positions: seq<int>)
    requires word.Length > 0
    requires forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= fileContent.Length - word.Length
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

    // Use KMP to find all match positions, then print matching lines with highlighting on the pattern
    var positions := search(word, buffer);
    PrintSearchResult(word, buffer, positions);
    
    // Close the file
    var closeOk := file.Close();
    if !closeOk {
        print "Error: Failed to close file\n";
        return;
    }

}

