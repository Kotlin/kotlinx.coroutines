From iris.heap_lang Require Import proofmode notation lang.

Definition make_array : val :=
  rec: "make_array" "k" "v" :=
    if: "k" ≤ #0
    then ref #()
    else let: "head" := ref "v" in
         let: "tail" := "make_array" ("k" - #1) "v" in
         ref ("head", "tail")%E.

Definition array_load : val :=
  rec: "array_load" "arr" "k" :=
    let: "head" := Fst (!"arr") in
    let: "tail" := Snd (!"arr") in
    if: "k" ≤ #0 then !"head" else "array_load" "tail" ("k" - #1).

Definition array_store : val :=
  rec: "array_store" "arr" "k" "v" :=
    let: "head" := Fst (!"arr") in
    let: "tail" := Snd (!"arr") in
    if: "k" ≤ #0 then "head" <- "v" else "array_store" "tail" ("k" - #1) "v".
