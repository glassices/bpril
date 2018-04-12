needs "bpril/rthm.ml";;

let split (c : string) (s : string) : (string list) =
  let ls = explode s in
  let rec work ls : (string * string list) =
    match ls with
      h::t -> let cnt,res = work t in
              if h = c then "",cnt::res
              else h ^ cnt,res
    | [] -> "",[] in
  let cnt,res = work ls in
  cnt::res;;

module Dii = Map.Make(struct type t = int let compare = compare end);;
let mm = ref Dii.empty;;

let main() =
  let fin = open_in "bpril/out" in

  let refl = mk_rthm (REFL `x`) in
  let assume = mk_rthm (ASSUME `x:bool`) in
  let T_TAUT = DEDUCT_ANTISYM_RULE (ASSUME `t:bool`) TRUTH in
  let t_taut = mk_rthm(T_TAUT) in

  try while true do
        let line = input_line fin in
        let lst = split "\t" line in
        let rname = hd lst and id = int_of_string (hd (tl lst)) in
        if rname = "axiom" then mm := Dii.add id (mk_rthm(Array.get arr id)) !mm
        else if id = 9 then mm := Dii.add id t_taut !mm
        else (
          printf "%d\n%!" id;
          let arg1 = el 2 lst and arg2 = el 3 lst in
          let rth1 = if arg1 = "refl" then refl
                     else if arg1 = "assume" then assume
                     else Dii.find (int_of_string arg1) !mm in
          let rth2 = if arg2 = "refl" then refl
                     else if arg2 = "assume" then assume
                     else Dii.find (int_of_string arg2) !mm in
          let ans = if rname = "eq_mp" then req_mp rth1 rth2
                    else if rname = "mk_comb" then rmk_comb rth1 rth2
                    else if rname = "trans" then rtrans rth1 rth2
                    else rdeduct rth1 rth2 in
          print_endline "done infer";
          try let rth = List.find (fun x -> rmatchable x (mk_rthm(Array.get arr id))) ans in
               mm := Dii.add id rth !mm;
          with Not_found -> failwith (Printf.sprintf "main[fatal]: fail at %d" id)
        )
      done
  with End_of_file ->
    close_in fin;
    print_endline "all checked";;

try main()
with Failure s -> print_endline s;;
(*
let rth1 = Dii.find 89 !mm;;
let rth2 = Dii.find 71 !mm;;
*)

let refl = mk_rthm(REFL `x:A`);;
let assume = mk_rthm(ASSUME `x:bool`);;
let r1 = el 0 (rmk_comb refl assume);;


