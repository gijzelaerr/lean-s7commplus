import LeanS7CommPlus

/-!
Decoder oracle for the differential fuzzer (integration/fuzz.py). Each input line is
`KIND HEX`; each output line is `ok RESULT CONSUMED` or `err`. RESULT is the value
in the Python reference's representation:

- `u32`, `u64`, `i32`, `i64`: a VLQ, as a decimal number;
- `pvalue`: a scalar PValue, as the hex of the bytes `decode_pvalue_to_bytes` returns
  (VLQ integers re-packed to their fixed width, BLOB and WSTRING as their bytes).
-/

open LeanS7 LeanS7CommPlus

def hexValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)
  else none

def parseHex (text : String) : Option ByteArray := do
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | high :: low :: rest => do
      let h ← hexValue high
      let l ← hexValue low
      pure (UInt8.ofNat (h * 16 + l) :: (← go rest))
    | _ => none
  pure (← go text.toList).toByteArray

def toHex (data : ByteArray) : String :=
  String.join (data.toList.map fun byte =>
    let digits := Nat.toDigits 16 byte.toNat
    String.ofList (if digits.length == 1 then '0' :: digits else digits))

/-- The bytes `decode_pvalue_to_bytes` returns for a value. -/
def pythonRaw : PValue → ByteArray
  | .null => ByteArray.empty
  | .udint value | .aid value => uint32BE value
  | .ulint value => uint64BE value
  | .dint value => uint32BE value.toUInt32
  | .lint value | .timespan value => uint64BE value.toUInt64
  | .blob _ data => data
  | .wstring utf8 => utf8
  | value => value.encodeBody

def decodeLine (kind : String) (data : ByteArray) : String :=
  let cursor : Cursor := { data }
  let result : Except DecodeError (String × Nat) :=
    match kind with
    | "u32" => (Vlq.decodeUInt32 cursor).map fun (v, c) => (toString v.toNat, c.offset)
    | "u64" => (Vlq.decodeUInt64 cursor).map fun (v, c) => (toString v.toNat, c.offset)
    | "i32" => (Vlq.decodeInt32 cursor).map fun (v, c) => (toString v.toInt, c.offset)
    | "i64" => (Vlq.decodeInt64 cursor).map fun (v, c) => (toString v.toInt, c.offset)
    | "pvalue" => (decodePValue cursor).map fun (v, c) => (toHex (pythonRaw v), c.offset)
    | _ => .error (.invalidField 0 "unknown kind")
  match result with
  | .ok (value, consumed) => s!"ok {value} {consumed}"
  | .error _ => "err"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let parts := line.trimAsciiEnd.toString.splitOn " "
  let output := match parts with
    | [kind, hex] => match parseHex hex with
      | some data => decodeLine kind data
      | none => "err"
    | [kind] => decodeLine kind ByteArray.empty
    | _ => "err"
  stdout.putStrLn output
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
