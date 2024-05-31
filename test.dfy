include "methods.dfy"

method Main()
{
    var randomSeq: seq<int> := [
    //   0,  1,   2,  3,  4,   5,   6,  7,  8,  9, 10, 11,  12, 13, 14, 15
        13, -3, -25, 20, -3, -16, -23, 18, 20, -7, 12, -5, -22, 15, -4, 7
    ];

    var low := 0;
    var high := |randomSeq| - 1;

    var start, end, sum := FindMaximumSegmentSum(randomSeq, low, high);

    print "The maximum subarray sum is: ";
    print sum;
    print "\n";
    print "It is beween these 0-index positions: ";
    print start;
    print " ";
    print end;
    print "\n";
}
