module Ints {
  const U32_BOUND: nat := 0x1_0000_0000
  newtype u32 = x:int | 0 <= x < 0x1_0000_0000
  newtype i32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
}

module Lang {
  import opened Ints

  datatype Reg = R0 | R1 | R2 | R3

  datatype Expr =
    | Const(n: u32)
      // overflow during addition is an error
    | Add(r1: Reg, r2: Reg)
      // this is saturating subtraction (to allow comparing numbers)
    | Sub(r1: Reg, r2: Reg)

  datatype Stmt =
    | Assign(r: Reg, e: Expr)
      // Jump by offset if condition is true
    | JmpZero(r: Reg, offset: i32)

  datatype Program = Program(stmts: seq<Stmt>)

}

/* Well-formed check: offsets are all within the program */
/* Main safety property: additions do not overflow */

/* First, we give the concrete semantics of programs. */

module ConcreteEval {
  import opened Ints
  import opened Lang

  type State = Reg -> u32

  function update_state(s: State, r0: Reg, v: u32): State {
    ((r: Reg) => if r == r0 then v else s(r))
  }

  datatype Option<T> = Some(v: T) | None

  function expr_eval(env: State, e: Expr): Option<u32>
  {
    match e {
      case Const(n) => Some(n)
      case Add(r1, r2) =>
        (if (env(r1) as int + env(r2) as int >= U32_BOUND) then None
         else Some(env(r1) + env(r2)))
      case Sub(r1, r2) =>
        (if env(r1) as int - env(r2) as int < 0 then Some(0)
         else Some(env(r1) - env(r2)))
    }
  }

  // stmt_step executes a single statement
  //
  // Returns a new state and a relative PC offset (which is 1 for non-jump
  // statements).
  function stmt_step(env: State, s: Stmt): Option<(State, int)> {
    match s {
      case Assign(r, e) =>
        var e' := expr_eval(env, e);
        match e' {
          case Some(v) => Some((update_state(env, r, v), 1))
          case None => None
        }
      case JmpZero(r, offset) =>
        Some((env, (if env(r) == 0 then offset else 1) as int))
    }
  }

  datatype ExecResult = Ok(env: State) | NoFuel | Error

  // Run a program starting at pc.
  //
  // The sequence of statements is constant, meant to reflect a static program.
  // Termination occurs if the pc ever reaches exactly the end.
  //
  // Errors can come from either executing statements (see stmt_step for those
  // errors), or from an out-of-bounds pc (negative or not past the end of ss).
  //
  // fuel is needed to make this function terminate; the idea is that if there
  // exists some fuel that makes the program terminate, that is it's complete
  // execution, and if it always runs out of fuel it has an infinite loop.
  function stmts_step(env: State, ss: seq<Stmt>, pc: nat, fuel: nat): ExecResult
    requires pc <= |ss|
    decreases fuel
  {
    if fuel == 0 then NoFuel
    else if pc == |ss| then Ok(env)
    else match stmt_step(env, ss[pc]) {
           case None => Error
           case Some((env', offset)) =>
             if !(0 <= pc + offset <= |ss|) then Error
             else stmts_step(env', ss, pc + offset, fuel - 1)
         }
  }

}

/* Now we turn to analyzing programs */

module AbstractEval {
  import opened Ints
  import opened Lang

  datatype Val = Interval(lo: int, hi: int)

  datatype AbstractState = AbstractState(rs: Reg -> Val)

  function expr_eval(env: AbstractState, e: Expr): Val {
    match e {
      case Const(n) => Interval(n as int, n as int)
      case Add(r1, r2) =>
        var v1 := env.rs(r1);
        var v2 := env.rs(r2);
        Interval(v1.lo + v2.lo, v1.hi + v2.hi)
      case Sub(r1, r2) =>
        // this was quite buggy initially: low is bounded (due to saturating
        // subtraction), and upper bound also should cannot go negative
        var v1 := env.rs(r1);
        var v2 := env.rs(r2);
        Interval(0, if v1.hi - v2.lo >= 0 then v1.hi - v2.lo else 0)
    }
  }

  function update_state(env: AbstractState, r0: Reg, v: Val): AbstractState {
    AbstractState((r: Reg) => if r == r0 then v else env.rs(r))
  }

  // function stmt_step(env: State, s: Stmt): Option<(State, int)>
  function stmt_eval(env: AbstractState, s: Stmt): (AbstractState, set<int>) {
    match s {
      case Assign(r, e) => var v := expr_eval(env, e);
                           (update_state(env, r, v), {1 as int})
      case JmpZero(r, offset) =>
        // imprecise analysis: we don't try to prove that this jump is or isn't taken
        (env, {offset as int, 1})
    }
  }

  /* TODO(tej): to interpret a program, we need to explore all paths. Along the
   * way, we would have to look for loops - our plan is to disallow them (unlike
   * a normal abstract interpretation which would try to run till a fixpoint). */

  // Implement a check for just the jump targets, which are static and thus
  // don't even need abstract interpretation.

  // Check that jump targets ss[from..] are valid.
  function has_valid_jump_targets(ss: seq<Stmt>, from: nat): bool
    decreases |ss|-from
    requires from <= |ss|
  {
    if from == |ss| then true
    else (match ss[from] {
            case JmpZero(_, offset) =>
              0 <= from + offset as int <= |ss|
            case _ => true
          } &&
          has_valid_jump_targets(ss, from+1))
  }

  ghost predicate valid_jump_targets(ss: seq<Stmt>) {
    forall i | 0 <= i < |ss| :: ss[i].JmpZero? ==> 0 <= i + ss[i].offset as int <= |ss|
  }

  lemma has_valid_jump_targets_ok_helper(ss: seq<Stmt>, from: nat)
    requires from <= |ss|
    decreases |ss|-from
    ensures has_valid_jump_targets(ss, from) <==>
            (forall i | from <= i < |ss| :: ss[i].JmpZero? ==> 0 <= i + ss[i].offset as int <= |ss|)
  {
  }

  lemma has_valid_jump_targets_ok(ss: seq<Stmt>)
    ensures has_valid_jump_targets(ss, 0) <==> valid_jump_targets(ss)
  {
    has_valid_jump_targets_ok_helper(ss, 0);
  }
}

module AbstractEvalProof {
  import opened Ints
  import opened Lang
  import E = ConcreteEval
  import opened AbstractEval

  /* What does it mean for a concrete state to be captured by an abstract state?
   * (Alternately, interpret each abstract state as a set of concrete states) */

  ghost predicate reg_included(c_v: u32, v: Val) {
    v.lo <= c_v as int <= v.hi
  }

  ghost predicate state_included(env: E.State, abs: AbstractState) {
    forall r: Reg :: reg_included(env(r), abs.rs(r))
  }

  lemma expr_eval_ok(env: E.State, abs: AbstractState, e: Expr)
    requires state_included(env, abs)
    requires E.expr_eval(env, e).Some?
    ensures reg_included(E.expr_eval(env, e).v, expr_eval(abs, e))
  {
    match e {
      case Add(_, _) => { return; }
      case Const(_) => { return; }
      case Sub(r1, r2) => {
        /* debugging bug in the abstract interpretation */
        assert reg_included(env(r1), abs.rs(r1));
        assert reg_included(env(r2), abs.rs(r2));
        assert env(r1) as int <= abs.rs(r1).hi;
        assert env(r2) as int >= abs.rs(r2).lo;
        if env(r1) <= env(r2) {
          assert E.expr_eval(env, e).v == 0;
          return;
        }
        assert E.expr_eval(env, e).v as int == env(r1) as int - env(r2) as int;
        return;
      }
    }
  }

  lemma stmt_eval_ok(env: E.State, abs: AbstractState, stmt: Stmt)
    requires state_included(env, abs)
    requires E.stmt_step(env, stmt).Some?
    ensures state_included(E.stmt_step(env, stmt).v.0, stmt_eval(abs, stmt).0)
  {}
}

