open List
open Sets


(* Types *)


type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}


(* Utility *)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

(* Helper for move *)
let rec helper_checkDelta delta head option = 
  match delta with 
  |[] -> [] 
  |h::t -> match h with 
    |(a, b, c) -> if a = head && b = option then [c] @ helper_checkDelta t head option else helper_checkDelta t head option 
;;

(* Helper for move *)
let rec helper_iState nfa list option = 
  match list with 
  |[] -> []
  |h::t -> union (helper_checkDelta nfa.delta h option) (helper_iState nfa t option)
;;

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  helper_iState nfa qs s
;;

(* Helper for eclosure *)
let rec helper_eclosure nfa iState list= 
  match iState with 
  | [] -> []
  | h::t -> if (elem h list) != true then let newlist = helper_checkDelta nfa.delta h None 
        in 
        union [h] (helper_eclosure nfa (union t newlist) (union list [h]))
      else helper_eclosure nfa t list
;;

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  helper_eclosure nfa qs []
;;


(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

(* Helper for new_states *)
let rec helper_states nfa sigma qs = 
  match sigma with 
  |[] -> [] 
  |h::t -> [e_closure nfa (move nfa qs (Some h))] @ helper_states nfa t qs 
;;
  
(* Helper for new_trans *)
let rec helper_trans nfa sigma qs = 
  match sigma with 
  |[] -> [] 
  |h::t -> (qs, Some h, e_closure nfa (move nfa qs (Some h))) :: helper_trans nfa t qs 
;;

(* Helper for new_finals*)
let rec helper_finals fs qs list = 
  match fs with 
  |[] -> []
  |h::t -> if elem h qs = true then [list] else helper_finals t qs list
;;


let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  helper_states nfa (nfa.sigma) qs
;;

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  helper_trans nfa nfa.sigma qs
;;


let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  let list = qs in 
  helper_finals (nfa.fs) qs list 
;;

(***** HELPERS FOR NFA_TO_DFA *****)

(* Get's final state *)
let rec helper_dfa_final nfa r = 
  match r with 
  |[] -> [] 
  |h::t -> new_finals nfa h @ helper_dfa_final nfa t 
  
;;

(* Get's qs states *)
let rec helper_dfa_states nfa dfa r =
  match r with 
  |[] -> []
  |h::t -> if elem h dfa.qs = false then remove [] (helper_states nfa nfa.sigma h) @ helper_dfa_states nfa dfa t else helper_dfa_states nfa dfa t
;; 

(* Get's the transitions *)
let rec helper_dfa_transitions nfa r = 
  match r with 
  |[] -> []
  |h::t -> new_trans nfa h @ helper_dfa_transitions nfa t 
;;

  
let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
  let work = union work (helper_dfa_states nfa dfa work) in 
  let work = remove [] (minus work dfa.qs) in 
  let transitions = helper_dfa_transitions nfa work in 
  match work with 
  |[] -> dfa
  |h::t -> 
      match dfa with 
      | { sigma = a
        ; qs = b 
        ; q0 = c
        ; fs = d 
        ; delta = e } -> let newdfa = { sigma = a
                                      ; qs = remove [] (union b (h :: b))
                                      ; q0 = c
                                      ; fs = d 
                                      ; delta = union e transitions }
          in 
          nfa_to_dfa_step nfa newdfa t 
;;
  ;;
let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  let q0state = e_closure nfa [nfa.q0]in 
  let wrk =[q0state] in 
  let dfa = 
    { sigma = nfa.sigma
    ; qs = []
    ; q0 = q0state
    ; fs = []
    ; delta = [] } in 
  let finaldfa = nfa_to_dfa_step nfa dfa wrk in
  match finaldfa with 
    { sigma = a
    ; qs = b 
    ; q0 = c
    ; fs = d 
    ; delta = e } -> let newdfa = { sigma = a
                                  ; qs =  b
                                  ; q0 = c
                                  ; fs = helper_dfa_final nfa b
                                  ; delta = e } in newdfa
;;

(* Helper for accept *)
let rec helper_accept2 fs finalposition =
  match fs with 
  |[] -> false
  |h::t -> if elem h finalposition then true else helper_accept2 t finalposition
;;
  
(* Helper for accept *)
let rec helper_accept nfa istate charlist = 
  match charlist with 
  | [] -> istate
  | h::t -> helper_accept nfa (move nfa (e_closure nfa istate) (Some h)) t
;;

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let charlist = explode s in 
  let finalposition = helper_accept nfa [nfa.q0] charlist  in 
  if helper_accept2 nfa.fs (e_closure nfa finalposition) = true then true else false
;;












