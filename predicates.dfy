function SumSegment(s: seq<int>, a: nat, b: nat): int
    requires a <= b < |s|
    decreases b - a
{
    if a == b then s[b] else SumSegment(s, a, b - 1) + s[b]
}

function ReverseSumSegment(s: seq<int>, a: nat, b: nat): int
    requires a <= b < |s|
    decreases b - a
{
    if a == b then s[a] else s[a] + SumSegment(s, a + 1, b)
}

lemma SumOrderLemma(s: seq<int>, a: nat, b: nat)
    requires a <= b < |s|
    ensures SumSegment(s, a, b) == ReverseSumSegment(s, a, b)
{}

lemma AppendSumsLemma(s: seq<int>, a: nat, b: nat, c:nat)
    requires a <= b < c < |s|
    ensures SumSegment(s, a, b) + SumSegment(s, b + 1, c) == SumSegment(s, a, c)
{}

predicate MaximumSlidingSegmentSum(s:seq<int>, low:nat, high:nat, start:nat, end:nat)
    requires |s| > 0
    requires low <= start <= end <= high < |s|
{
    var cachedSum := SumSegment(s, start, end);
    forall i, j :: low <= i <= j <= high ==>
        SumSegment(s, i, j) <= cachedSum
}

predicate MaximumCrossingSegmentSum(s:seq<int>, low:nat, mid:nat, high:nat, start:nat, end:nat)
    requires |s| > 0
    requires low <= start <= mid < end <= high < |s|
{
    var cachedSum := SumSegment(s, start, end);
    forall i, j :: low <= i <= mid < j <= high ==>
        SumSegment(s, i, j) <= cachedSum
}

predicate MaximumFixedTailSegmentSum(s:seq<int>, low:nat, high:nat, start:nat)
    requires |s| > 0
    requires low <= start <= high < |s|
{
    var cachedSum := SumSegment(s, start, high);
    forall i :: low <= i <= high ==>
        SumSegment(s, i, high) <= cachedSum
}

predicate MaximumFixedHeadSegmentSum(s:seq<int>, low:nat, high:nat, end:nat)
    requires |s| > 0
    requires low <= end <= high < |s|
{
    var cachedSum := SumSegment(s, low, end);
    forall i :: low <= i <= high ==>
        SumSegment(s, low, i) <= cachedSum
}

lemma CrossingLemma(
    s:seq<int>,
    low:nat, mid:nat, high:nat,
    start:nat, end:nat
)
    requires |s| > 0
    requires low <= start <= mid < end <= high < |s|

    requires MaximumFixedTailSegmentSum(s, low, mid, start)
    requires MaximumFixedHeadSegmentSum(s, mid + 1, high, end)

    ensures MaximumCrossingSegmentSum(s, low, mid, high, start, end)
{
    forall i, j | low <= i <= mid < j <= high
        ensures SumSegment(s, i, j) <= SumSegment(s, start, end)
    {
        assert SumSegment(s, i, mid) + SumSegment(s, mid + 1, j) <= SumSegment(s, start, mid) + SumSegment(s, mid + 1, end);
        AppendSumsLemma(s, i, mid, j);
        AppendSumsLemma(s, start, mid, end);
        assert SumSegment(s, i, j) <= SumSegment(s, start, end);
    }
}
