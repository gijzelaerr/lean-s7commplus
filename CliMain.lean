import LeanS7CommPlus

/-!
A command-line client for the integration tests:

    lean-s7commplus-cli HOST PORT read DB START SIZE    prints the bytes as hex
    lean-s7commplus-cli HOST PORT write DB START HEX
    lean-s7commplus-cli HOST PORT browse                prints "number name" per data block
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

def usage : String :=
  "usage: lean-s7commplus-cli HOST PORT (read DB START SIZE | write DB START HEX | browse)"

def run (args : List String) : IO UInt32 := do
  match args with
  | host :: portText :: command => do
    let some port := portText.toNat? | IO.eprintln usage; return 2
    let client ← Client.connect host (UInt16.ofNat port)
    match command with
    | ["read", db, start, size] =>
      let (some db, some start, some size) := (db.toNat?, start.toNat?, size.toNat?)
        | IO.eprintln usage; return 2
      let (client, data) ← client.readDb (UInt16.ofNat db) (UInt32.ofNat start) (UInt32.ofNat size)
      IO.println (toHex data)
      client.close
    | ["write", db, start, hex] =>
      let (some db, some start, some data) := (db.toNat?, start.toNat?, parseHex hex)
        | IO.eprintln usage; return 2
      let client ← client.writeDb (UInt16.ofNat db) (UInt32.ofNat start) data
      client.close
    | ["browse"] =>
      let (client, blocks) ← client.listDataBlocks
      for (_, name, number) in blocks do
        IO.println s!"{number} {name}"
      client.close
    | _ => IO.eprintln usage; return 2
    return 0
  | _ => IO.eprintln usage; return 2

def main (args : List String) : IO UInt32 := do
  try run args
  catch error =>
    IO.eprintln s!"error: {error}"
    return 1
