From iris.proofmode Require Import tactics.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation lang.

Definition getAndUpdate : val :=
  rec: "getAndUpdate" "l" "f" :=
    let: "o" := ! "l" in
    match: "f" "o" with
      NONE => NONE
    | SOME "v" => if: CAS "l" "o" "v"
                  then SOME "o"
                  else "getAndUpdate" "l" "f"
    end.
