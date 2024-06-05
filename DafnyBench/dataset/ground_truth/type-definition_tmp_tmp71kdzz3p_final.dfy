// -------------------------------------------------------------
// 1. Implementing type inference
// -------------------------------------------------------------

// Syntax:
//
// τ := Int | Bool | τ1->τ2
// e ::= x | λx : τ.e | true| false| e1 e2 | if e then e1 else e2
// v ::= true | false | λx : τ.e
// E ::= [·] | E e | v E | if E then e1 else e2
type VarName = string

type TypeVar = Type -> Type

datatype Type = Int | Bool | TypeVar

datatype Exp =
    | Var(x: VarName)
    | Lam(x: VarName, t: Type, e: Exp)
    | App(e1: Exp, e2:Exp)
    | True()
    | False()
    | Cond(e0: Exp, e1: Exp, e2: Exp)

datatype Value =
    | TrueB()
    | FalseB()
    | Lam(x: VarName, t: Type, e: Exp)

datatype Eva = 
    | E()
    | EExp(E : Eva, e : Exp)
    | EVar(v : Value, E : Eva)
    | ECond(E:Eva, e1 : Exp, e2 : Exp)

function FV(e: Exp): set<VarName> {
    match(e) {
        case Var(x) => {x}
        case Lam(x, t, e) => FV(e) - {x} //不确定
        case App(e1,e2) => FV(e1) + FV(e2)
        case True() => {}
        case False() => {}
        case Cond(e0, e1, e2) => FV(e0) + FV(e1) + FV(e2)
    }
}
// Typing rules system
// -------------------------------------------------------------
// Typing rules system
type Env = map<VarName, Type>

predicate hasType(gamma: Env, e: Exp, t: Type)
{
    match e {

        case Var(x) =>  x in gamma && t == gamma[x]
        case Lam(x, t, e) => hasType(gamma, e, t)//错的
        case App(e1,e2) => hasType(gamma, e1, t) && hasType(gamma, e2, t)
        case True() => t == Bool
        case False() => t == Bool
        case Cond(e0, e1, e2) => hasType(gamma, e0, Bool) && hasType(gamma, e1, t) && hasType(gamma, e2, t)
    }    
}

// -----------------------------------------------------------------
// 2. Extending While with tuples
// -----------------------------------------------------------------


/*lemma {:induction false} extendGamma(gamma: Env, e: Exp, t: Type, x1: VarName, t1: Type)
    requires hasType(gamma, e, t)
    requires x1 !in FV(e)
    ensures hasType(gamma[x1 := t1], e, t)
{
    match e {
        case Var(x) => {
            assert x in FV(e);
            assert x != x1;
            assert gamma[x1 := t1][x] == gamma[x];
            assert hasType(gamma[x1 := t1], e, t);
        }
        case True() => {
            assert t == Bool;
        }
        case False() => {
            assert t == Bool;
        }
        //case Lam(x, t, e)
        case App(e1, e2) =>{
            calc{
                hasType(gamma, e, t);
                ==>
                    hasType(gamma, e1, TypeVar) && hasType(gamma, e2, t);
                ==> { extendGamma(gamma, e1, TypeVar, x1, t2); }
                    hasType(gamma[x1 := t1], e1, TypeVar) && hasType(gamma, e2, t);
                ==> { extendGamma(gamma, e1, t, x1, t1); }
                    hasType(gamma[x1 := t1], e0, Bool) && hasType(gamma[x1 := t1], e1, t) && hasType(gamma, e2, t);
                ==> { extendGamma(gamma, e2, t, x1, t1); }
                    hasType(gamma[x1 := t1], e0, Bool) && hasType(gamma[x1 := t1], e1, t) && hasType(gamma[x1 := t1], e2, t);
                ==> 
                    hasType(gamma[x1 := t1], e, t);
            }
        }
        case Cond(e0, e1, e2) =>  {
            calc {
                    hasType(gamma, e, t);
                ==>
                    hasType(gamma, e0, Bool) && hasType(gamma, e1, t) && hasType(gamma, e2, t);
                ==> { extendGamma(gamma, e0, Bool, x1, t1); }
                    hasType(gamma[x1 := t1], e0, Bool) && hasType(gamma, e1, t) && hasType(gamma, e2, t);
                ==> { extendGamma(gamma, e1, t, x1, t1); }
                    hasType(gamma[x1 := t1], e0, Bool) && hasType(gamma[x1 := t1], e1, t) && hasType(gamma, e2, t);
                ==> { extendGamma(gamma, e2, t, x1, t1); }
                    hasType(gamma[x1 := t1], e0, Bool) && hasType(gamma[x1 := t1], e1, t) && hasType(gamma[x1 := t1], e2, t);
                ==> 
                    hasType(gamma[x1 := t1], e, t);
            }                           
        }
    }
}    
