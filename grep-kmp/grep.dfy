/*  
 * This is the skeleton for the grep utility.
 * In this folder you should include a grep utility based
 * on the Knuth-Morris-Pratt algorithm.
 *
 */

include "Io.dfy"

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
    if word[i] == word[len] {
      len := len + 1;
      lps[i] := len;
      i := i + 1;
    }
    else {
      if len != 0 {
        len := lps[len - 1];
      }
      else {
        lps[i] := 0;
        i := i + 1;
      }
    }
  }
}

method search(word: array<char>, txt: array<byte>) returns (positions: seq<int>)
    requires word.Length > 0
    ensures forall i :: 0 <= i < |positions| ==> 0 <= positions[i] <= txt.Length - word.Length
{
    var lps := constructLps(word);

    var n := txt.Length;
    var m := word.Length;
    positions := [];
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
        if j < m && txt[i] as char == word[j] {
            i := i + 1;
            j := j + 1;

            if j == m {
                positions := positions + [i-j];
                j := 0;
            }
        }
        else {
            if j != 0 {
                j := lps[j - 1];
            }
            else {
                i := i + 1;
            }
        }
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

    var positions := search(word, buffer);

    // Output result (YES: all positions or NO)
    PrintSearchResult(positions);
    
    // Close the file
    var closeOk := file.Close();
    if !closeOk {
        print "Error: Failed to close file\n";
        return;
    }

}

