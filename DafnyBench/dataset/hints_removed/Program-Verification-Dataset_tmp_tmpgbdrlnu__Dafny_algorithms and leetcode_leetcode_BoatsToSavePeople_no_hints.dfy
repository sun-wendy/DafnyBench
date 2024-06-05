/*
function numRescueBoats(people: number[], limit: number): number {
    //people.sort((a,b) => a-b);
    binsort(people, limit);
    let boats = 0;
    let lower = 0, upper = people.length-1; 
    while(lower <= upper) {
        if(people[upper] == limit || people[upper]+people[lower] > limit) {
            boats++
            upper--;
        }else if(people[upper]+people[lower] <= limit) {
            upper--;
            lower++;
            boats++;
        }
    }

    return boats;
};
nums[k++] = i+1;
function binsort(nums: number[], limit: number) {
    let result = new Array(limit);
    result.fill(0);
    for(let i = 0; i < nums.length; i++) {
        result[nums[i]-1]++;
    }
    var k = 0;
    for(let i=0; i < result.length; i++) {
        for(let j = 0; j < result[i]; j++) {
            nums[k++] = i+1;
        }
    }
}
*/

function sumBoat(s: seq<nat>): nat 
    requires 1 <= |s| <= 2
{
    if |s| == 1 then s[0] else s[0] + s[1]
}

predicate isSafeBoat(boat: seq<nat>, limit: nat) {
    1 <= |boat| <= 2 && sumBoat(boat) <= limit
}

function multisetAdd(ss: seq<seq<nat>>): multiset<nat> {
    if ss == [] then multiset{} else multiset(ss[0]) + multisetAdd(ss[1..])
}

predicate multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>) {
    multiset(xs) == multisetAdd(ss)
}

predicate allSafe(boats: seq<seq<nat>>, limit: nat) {
    forall boat :: boat in boats ==> isSafeBoat(boat, limit)
}

predicate sorted(list: seq<int>)
{
    forall i,j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
    requires |people| >= 1
    requires sorted(people)
    requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
    ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|// && forall boatConfigs :: multisetEqual(boatConfigs, people) && allSafe(boatConfigs, limit) ==> boats <= |boatConfigs|
{
    boats := 0;
    var lower: nat := 0;
    var upper: int := |people| - 1;
    ghost var visitedUpper: multiset<nat> := multiset{};
    ghost var visitedLower: multiset<nat> := multiset{};
    ghost var remaining: multiset<nat> := multiset(people);
    ghost var safeBoats: seq<seq<nat>> := [];
    while lower <= upper 
    {
        if people[upper] == limit || people[upper] + people[lower] > limit {
            boats := boats + 1;
            safeBoats := [[people[upper]]] + safeBoats;
            ghost var gu := people[upper+1..];
            visitedUpper := visitedUpper + multiset{people[upper]};
            upper := upper - 1;
        }else{
            ghost var gl := people[..lower];
            boats := boats + 1;
            if lower == upper {
                visitedLower := visitedLower + multiset{people[lower]};
                safeBoats := [[people[lower]]] + safeBoats;
            }else{
                ghost var gu := people[upper+1..];
                visitedUpper := visitedUpper + multiset{people[upper]};
                visitedLower := visitedLower + multiset{people[lower]};
                safeBoats := [[people[upper], people[lower]]] + safeBoats;
                upper := upper - 1;
            }
            lower := lower + 1;
        }
    }
}

/*
limit 3
[3,2,2,1]
lower = 0
upper = 3

upper = 2
lower= 0

lower = 1
upper = 1

lower = 2 [..2]
upper = 1 [2..]
*/
