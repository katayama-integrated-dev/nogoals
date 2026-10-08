/-
  Strict JSON field access shared by the facts and html-validate decoders:
  every getter names the context it is decoding and fails on a missing key
  or a wrong type — a schema drift is an error, never a default.
-/

import Lean.Data.Json

namespace NoGoals.Verify.Json

open Lean (Json)

def parse (what : String) (s : String) : Except String Json :=
  match Lean.Json.parse s with
  | .ok j => .ok j
  | .error e => .error s!"{what} is not JSON: {e}"

def getStr (j : Json) (k ctx : String) : Except String String :=
  match j.getObjVal? k with
  | .ok (.str s) => .ok s
  | .ok _ => .error s!"{ctx}: `{k}` must be a string"
  | .error _ => .error s!"{ctx}: missing `{k}`"

def getNat (j : Json) (k ctx : String) : Except String Nat :=
  match j.getObjVal? k with
  | .ok v => match v.getNat? with
    | .ok n => .ok n
    | .error _ => .error s!"{ctx}: `{k}` must be a non-negative integer"
  | .error _ => .error s!"{ctx}: missing `{k}`"

def getBool (j : Json) (k ctx : String) : Except String Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => .ok b
  | .ok _ => .error s!"{ctx}: `{k}` must be a boolean"
  | .error _ => .error s!"{ctx}: missing `{k}`"

def getArr (j : Json) (k ctx : String) : Except String (List Json) :=
  match j.getObjVal? k with
  | .ok (.arr a) => .ok a.toList
  | .ok _ => .error s!"{ctx}: `{k}` must be an array"
  | .error _ => .error s!"{ctx}: missing `{k}`"

def getStrList (j : Json) (k ctx : String) : Except String (List String) := do
  let xs ← getArr j k ctx
  xs.mapM fun x => match x with
    | .str s => pure s
    | _ => throw s!"{ctx}: `{k}` must contain only strings"

/-- The object must have exactly these keys — no more, no fewer. -/
def expectKeys (j : Json) (keys : List String) (ctx : String) : Except String Unit := do
  match j with
  | .obj kvs =>
    let present := kvs.toArray.toList.map (·.1)
    for k in present do
      unless keys.contains k do throw s!"{ctx}: unknown key `{k}`"
    for k in keys do
      unless present.contains k do throw s!"{ctx}: missing key `{k}`"
  | _ => throw s!"{ctx}: expected an object"

end NoGoals.Verify.Json
