module HOL : sig
  type 'a equal = {equal : 'a -> 'a -> bool}
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let rec eq _A a b = equal _A a b;;

end;; (*struct HOL*)

module Predicate : sig
  type 'a seq
  type 'a pred
  val the : 'a HOL.equal -> 'a pred -> 'a
  val bind : 'a pred -> ('a -> 'b pred) -> 'b pred
  val bot_pred : 'a pred
  val single : 'a -> 'a pred
  val sup_pred : 'a pred -> 'a pred -> 'a pred
  val if_pred : bool -> unit pred
end = struct

type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);;

let rec is_empty (Seq f) = null (f ())
and null = function Empty -> true
           | Insert (x, p) -> false
           | Join (p, xq) -> is_empty p && null xq;;

let rec singleton _A
  default (Seq f) =
    (match f () with Empty -> default ()
      | Insert (x, p) ->
        (if is_empty p then x
          else (let y = singleton _A default p in
                 (if HOL.eq _A x y then x else default ())))
      | Join (p, xq) ->
        (if is_empty p then the_only _A default xq
          else (if null xq then singleton _A default p
                 else (let x = singleton _A default p in
                       let y = the_only _A default xq in
                        (if HOL.eq _A x y then x else default ())))))
and the_only _A
  default x1 = match default, x1 with default, Empty -> default ()
    | default, Insert (x, p) ->
        (if is_empty p then x
          else (let y = singleton _A default p in
                 (if HOL.eq _A x y then x else default ())))
    | default, Join (p, xq) ->
        (if is_empty p then the_only _A default xq
          else (if null xq then singleton _A default p
                 else (let x = singleton _A default p in
                       let y = the_only _A default xq in
                        (if HOL.eq _A x y then x else default ()))));;

let rec the _A
  a = singleton _A (fun _ -> failwith "not_unique" (fun _ -> the _A a)) a;;

let rec bind (Seq g) f = Seq (fun _ -> apply f (g ()))
and apply f x1 = match f, x1 with f, Empty -> Empty
            | f, Insert (x, p) -> Join (f x, Join (bind p f, Empty))
            | f, Join (p, xq) -> Join (bind p f, apply f xq);;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec adjunct p x1 = match p, x1 with p, Empty -> Join (p, Empty)
                  | p, Insert (x, q) -> Insert (x, sup_pred q p)
                  | p, Join (q, xq) -> Join (q, adjunct p xq)
and sup_pred
  (Seq f) (Seq g) =
    Seq (fun _ ->
          (match f () with Empty -> g ()
            | Insert (x, p) -> Insert (x, sup_pred p (Seq g))
            | Join (p, xq) -> adjunct (Seq g) (Join (p, xq))));;

let rec if_pred b = (if b then single () else bot_pred);;

end;; (*struct Predicate*)

module BoolExp : sig
  type boolexp = BTrue | BFalse | BIf of boolexp * boolexp * boolexp
  val bigstep_ex : boolexp -> boolexp
end = struct

type boolexp = BTrue | BFalse | BIf of boolexp * boolexp * boolexp;;

let rec equal_boolexpa
  x0 x1 = match x0, x1 with BFalse, BIf (x31, x32, x33) -> false
    | BIf (x31, x32, x33), BFalse -> false
    | BTrue, BIf (x31, x32, x33) -> false
    | BIf (x31, x32, x33), BTrue -> false
    | BTrue, BFalse -> false
    | BFalse, BTrue -> false
    | BIf (x31, x32, x33), BIf (y31, y32, y33) ->
        equal_boolexpa x31 y31 &&
          (equal_boolexpa x32 y32 && equal_boolexpa x33 y33)
    | BFalse, BFalse -> true
    | BTrue, BTrue -> true;;

let equal_boolexp = ({HOL.equal = equal_boolexpa} : boolexp HOL.equal);;

let rec is_value
  t = (match t with BTrue -> true | BFalse -> true | BIf (_, _, _) -> false);;

let rec bigstep
  x = Predicate.sup_pred
        (Predicate.bind (Predicate.single x)
          (fun xa ->
            Predicate.bind (Predicate.if_pred (is_value xa))
              (fun () -> Predicate.single xa)))
        (Predicate.sup_pred
          (Predicate.bind (Predicate.single x)
            (fun a ->
              (match a with BTrue -> Predicate.bot_pred
                | BFalse -> Predicate.bot_pred
                | BIf (t1, t2, _) ->
                  Predicate.bind (bigstep t1)
                    (fun aa ->
                      (match aa
                        with BTrue ->
                          Predicate.bind (bigstep t2) Predicate.single
                        | BFalse -> Predicate.bot_pred
                        | BIf (_, _, _) -> Predicate.bot_pred)))))
          (Predicate.bind (Predicate.single x)
            (fun a ->
              (match a with BTrue -> Predicate.bot_pred
                | BFalse -> Predicate.bot_pred
                | BIf (t1, _, t3) ->
                  Predicate.bind (bigstep t1)
                    (fun aa ->
                      (match aa with BTrue -> Predicate.bot_pred
                        | BFalse -> Predicate.bind (bigstep t3) Predicate.single
                        | BIf (_, _, _) -> Predicate.bot_pred))))));;

let rec bigstep_ex t = Predicate.the equal_boolexp (bigstep t);;

end;; (*struct BoolExp*)
