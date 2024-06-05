function reverse(xs: seq<nat>): seq<nat>
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if {
        case xs == [] =>
        calc {
            reverse([] + ys);
            calc {
                [] + ys;
                ys;
            }
            reverse(ys);
            reverse(ys) + reverse([]);
        }
        case xs != [] => {
            var zs := xs + ys;
            assert zs[1..] == xs[1..] + ys;
        }
    }
}

lemma ReverseInvolution(xxs: seq<nat>)
ensures reverse(reverse(xxs)) == xxs
{
    if {
        case xxs == [] => {}
        case xxs != [] => calc {
            reverse(reverse(xxs));
            ==
            reverse(reverse(xxs[1..]) + [xxs[0]]);
            ==
            { ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]); }
            reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
            ==
            { ReverseInvolution(xxs[1..]); }
            calc {
                reverse([xxs[0]]);
                ==
                [] + [xxs[0]];
                ==
                [xxs[0]];
            }
            [xxs[0]] + xxs[1..];
            ==
            xxs;
        }
    }
}

