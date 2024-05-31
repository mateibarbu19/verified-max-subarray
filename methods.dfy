include "predicates.dfy"

method FindMaximumCrossingSegmentSum(s:seq<int>, low:nat, mid:nat, high:nat)
    returns (start:nat, end:nat, maxCrossSum:int)

    requires |s| > 0
    requires low <= mid < high < |s|

    ensures low <= start <= mid < end <= high < |s|

    ensures MaximumCrossingSegmentSum(s, low, mid, high, start, end)
    ensures maxCrossSum == SumSegment(s, start, end)
{
    var sum: int;
    var leftSum: int;
    var rightSum: int;

    start := mid;
    leftSum := s[mid];
    sum := leftSum;
    for i := mid downto low
        // for implicitly excludes mid
        invariant low <= i <= start <= mid
        invariant sum == SumSegment(s, i, mid)
        invariant leftSum == SumSegment(s, start, mid)
        invariant MaximumFixedTailSegmentSum(s, i, mid, start)
    {
        sum := sum + s[i];
        SumOrderLemma(s, i, mid);
        if sum > leftSum {
            leftSum := sum;
            start := i;
        }
    }

    end := mid + 1;
    rightSum := s[mid + 1];
    sum := rightSum;
    for j := mid + 2 to high + 1
        // for implicitly excludes high + 1
        invariant end <= high
        invariant mid < end < j <= high + 1
        invariant sum == SumSegment(s, mid + 1, j - 1)
        invariant rightSum == SumSegment(s, mid + 1, end)
        invariant MaximumFixedHeadSegmentSum(s, mid  + 1, j - 1, end)
    {
        sum := sum + s[j];
        if sum > rightSum {
            rightSum := sum;
            end := j;
        }
    }

    AppendSumsLemma(s, start, mid, end);
    CrossingLemma(s, low, mid, high, start, end);

    return start, end, leftSum + rightSum;
}

method FindMaximumSegmentSum(s:seq<int>, low:nat, high:nat)
    returns (start:nat, end:nat, maxSum:int)

    requires |s| > 0
    requires low <= high < |s|

    decreases high - low


    ensures low <= start <= end <= high < |s|

    ensures maxSum == SumSegment(s, start, end)
    ensures MaximumSlidingSegmentSum(s, low, high, start, end)
{
    if low == high {
        return low, high, s[low];
    }
    else {
        var mid: nat := (low + high) / 2;

        var leftStart, leftEnd, leftSum: int :=
            FindMaximumSegmentSum(s, low, mid);

        var rightStart, rightEnd, rightSum: int :=
            FindMaximumSegmentSum(s, mid + 1, high);

        var crossStart, crossEnd, crossSum: int :=
            FindMaximumCrossingSegmentSum(s, low, mid, high);

        if (crossSum >= leftSum && crossSum >= rightSum) {
            return crossStart, crossEnd, crossSum;
        }
        else if (leftSum >= crossSum && leftSum >= rightSum) {
            return leftStart, leftEnd, leftSum;
        }
        else {
            return rightStart, rightEnd, rightSum;
        }
    }
}
