import LeanS7CommPlus.Fragments
import LeanS7CommPlus.Message

/-!
# V3 frames over an abstract MAC

After SessionKey authentication every message travels in a V3 frame whose data is
the integrity envelope: `0x20`, a 32-byte digest, and the message. The digest is
HMAC-SHA256 of the message under the first 24 bytes of the session key.

This module proves the framing correct relative to any MAC with 32-byte tags. The
MAC itself (HMAC-SHA256) is not implemented here: computing it is open decision 3.

A response split over several fragments carries one envelope per fragment, and the
digests are chained. `ChainedMac` abstracts the chain as a state machine. Two of the
dialects the Python client accepts are instances of it over a plain MAC:
independent per-fragment HMACs and PLCSIM's feed-forward chain
`HMAC(key, digest₍ₙ₋₁₎ ‖ fragmentₙ)`. The state-resume dialect of real S7-1200/1500
firmware continues finalized SHA-256 states, so its instance needs SHA-256 internals
and waits for decision 3 too.

The theorems:

- `openV3_sealV3`, `openFragments_sealFragments`: round trips.
- `sealV3_of_openV3`, `openFragments_sound`: soundness. A frame is accepted only if
  it is exactly the seal of the message it yields, so forging an accepted frame for a
  message means producing that message's MAC tag.
-/

namespace LeanS7CommPlus

open LeanS7

/-- A message authentication code under a fixed key, with 32-byte tags. -/
structure Mac where
  tag : ByteArray → ByteArray
  tag_size : ∀ message, (tag message).size = 32

/-- Why a protected frame was refused. -/
inductive OpenError where
  | malformed (error : DecodeError)
  | wrongVersion (version : FrameVersion)
  | integrity
  deriving Repr

/-- A V3 frame around the message and its tag. -/
def sealV3 (mac : Mac) (message : ByteArray) : ByteArray :=
  encodeFrame .v3 (encodeIntegrityEnvelope (mac.tag message) message)

/-- Check a V3 frame and return its message. -/
def openV3 (mac : Mac) (frame : ByteArray) : Except OpenError ByteArray :=
  match decodeFrame frame with
  | .error error => .error (.malformed error)
  | .ok (version, data) =>
    if version ≠ .v3 then .error (.wrongVersion version)
    else match decodeIntegrityEnvelope data with
      | .error error => .error (.malformed error)
      | .ok (digest, message) => if digest = mac.tag message then .ok message else .error .integrity

/-- A chain of tags over the fragments of one response: a starting state, and for
    each fragment its tag and the next state. -/
structure ChainedMac (σ : Type) where
  start : σ
  next : σ → ByteArray → ByteArray × σ
  tag_size : ∀ state data, (next state data).1.size = 32

/-- Every fragment tagged on its own. -/
def ChainedMac.independent (mac : Mac) : ChainedMac Unit where
  start := ()
  next _ data := (mac.tag data, ())
  tag_size _ data := mac.tag_size data

/-- PLCSIM's feed-forward chain: the first fragment's tag is the MAC of its data, each
    later tag the MAC of the previous tag followed by the fragment's data. -/
def ChainedMac.feedForward (mac : Mac) : ChainedMac (Option ByteArray) where
  start := none
  next previous data :=
    let tag := mac.tag ((previous.getD ByteArray.empty) ++ data)
    (tag, some tag)
  tag_size _ _ := mac.tag_size _

/-- The envelopes of the fragments, each with its tag in the chain. -/
def ChainedMac.protect (chain : ChainedMac σ) : σ → List ByteArray → List ByteArray
  | _, [] => []
  | state, data :: rest =>
    let (tag, state) := chain.next state data
    encodeIntegrityEnvelope tag data :: chain.protect state rest

/-- Check each envelope against the chain and return the fragments' data. -/
def ChainedMac.check (chain : ChainedMac σ) : σ → List ByteArray → Except OpenError (List ByteArray)
  | _, [] => .ok []
  | state, envelope :: rest =>
    match decodeIntegrityEnvelope envelope with
    | .error error => .error (.malformed error)
    | .ok (digest, data) =>
      let (tag, state) := chain.next state data
      if digest = tag then
        match chain.check state rest with
        | .error error => .error error
        | .ok others => .ok (data :: others)
      else .error .integrity

/-- A response in V3 fragments, each fragment's data protected by the chain. -/
def sealFragments (chain : ChainedMac σ) (pieces : List ByteArray) : ByteArray :=
  encodeFragments .v3 (chain.protect chain.start pieces)

/-- Reassemble and check a V3 response. -/
def openFragments (chain : ChainedMac σ) (message : ByteArray) : Except OpenError ByteArray :=
  match decodeFragments message with
  | .error error => .error (.malformed error)
  | .ok (version, envelopes) =>
    if version ≠ .v3 then .error (.wrongVersion version)
    else match chain.check chain.start envelopes with
      | .error error => .error error
      | .ok pieces => .ok (joinFragments pieces)

/-! ## Single frames -/

theorem encodeIntegrityEnvelope_size (digest message : ByteArray) :
    (encodeIntegrityEnvelope digest message).size = 1 + digest.size + message.size := by
  simp [encodeIntegrityEnvelope, ByteArray.size_append, bytes_size]

theorem openV3_sealV3 (mac : Mac) (message : ByteArray) (hsize : message.size + 33 < 65536) :
    openV3 mac (sealV3 mac message) = .ok message := by
  have hdata : (encodeIntegrityEnvelope (mac.tag message) message).size < 65536 := by
    rw [encodeIntegrityEnvelope_size, mac.tag_size]; omega
  simp [openV3, sealV3, decodeFrame_encodeFrame _ _ hdata,
    decodeIntegrityEnvelope_encode _ _ (mac.tag_size message)]

/-- Soundness: a frame that `openV3` accepts is exactly the seal of its message. -/
theorem sealV3_of_openV3 (mac : Mac) (frame message : ByteArray) (h : openV3 mac frame = .ok message) :
    frame = sealV3 mac message := by
  unfold openV3 at h
  split at h
  · contradiction
  rename_i version data hframe
  split at h
  · contradiction
  rename_i hversion
  split at h
  · contradiction
  rename_i digest m henvelope
  split at h
  · rename_i hdigest
    injection h with h
    subst h
    simp only [ne_eq, Decidable.not_not] at hversion
    subst hversion
    have hf := decodeFrame_canonical _ _ _ hframe
    obtain ⟨_, he⟩ := decodeIntegrityEnvelope_canonical _ _ _ henvelope
    rw [← hf, ← he, hdigest]
    rfl
  · contradiction

/-! ## Fragmented responses -/

theorem ChainedMac.protect_length (chain : ChainedMac σ) (state : σ) (pieces : List ByteArray) :
    (chain.protect state pieces).length = pieces.length := by
  induction pieces generalizing state with
  | nil => rfl
  | cons data rest ih => simp [ChainedMac.protect, ih]

/-- The envelopes of fragments that fit with their envelope are `Fragmented`. -/
theorem ChainedMac.fragmented_protect (chain : ChainedMac σ) (state : σ) (pieces : List ByteArray)
    (hne : pieces ≠ []) (hsize : ∀ data ∈ pieces, data.size + 33 < 65536) :
    Fragmented (chain.protect state pieces) := by
  induction pieces generalizing state with
  | nil => contradiction
  | cons data rest ih =>
    have hd := hsize data (by simp)
    have henv : ∀ s, (encodeIntegrityEnvelope (chain.next s data).1 data).size = 33 + data.size := by
      intro s
      rw [encodeIntegrityEnvelope_size, chain.tag_size]
    cases rest with
    | nil =>
      exact .single _ (by rw [henv]; omega)
    | cons next others =>
      have tail := ih (chain.next state data).2 (by simp)
        (fun piece hpiece => hsize piece (by simp_all))
      have hn := hsize next (by simp)
      have hnext : ∀ s, (encodeIntegrityEnvelope (chain.next s next).1 next).size = 33 + next.size := by
        intro s
        rw [encodeIntegrityEnvelope_size, chain.tag_size]
      simp only [ChainedMac.protect] at tail ⊢
      exact .cons _ _ _ (by rw [henv]; omega) (by rw [henv]; omega) (by rw [hnext]; omega) tail

theorem ChainedMac.check_protect (chain : ChainedMac σ) (state : σ) (pieces : List ByteArray) :
    chain.check state (chain.protect state pieces) = .ok pieces := by
  induction pieces generalizing state with
  | nil => rfl
  | cons data rest ih =>
    simp [ChainedMac.protect, ChainedMac.check,
      decodeIntegrityEnvelope_encode _ _ (chain.tag_size state data), ih]

theorem ChainedMac.protect_of_check (chain : ChainedMac σ) (state : σ) (envelopes pieces : List ByteArray)
    (h : chain.check state envelopes = .ok pieces) : envelopes = chain.protect state pieces := by
  induction envelopes generalizing state pieces with
  | nil =>
    simp only [ChainedMac.check] at h
    injection h with h
    subst h
    rfl
  | cons envelope rest ih =>
    unfold ChainedMac.check at h
    split at h
    · contradiction
    rename_i digest data henvelope
    simp only at h
    split at h
    · rename_i hdigest
      split at h
      · contradiction
      rename_i others hrest
      injection h with h
      subst h
      obtain ⟨_, he⟩ := decodeIntegrityEnvelope_canonical _ _ _ henvelope
      simp only [ChainedMac.protect]
      rw [← ih _ _ hrest, ← he, hdigest]
    · contradiction

theorem openFragments_sealFragments (chain : ChainedMac σ) (pieces : List ByteArray)
    (hne : pieces ≠ []) (hsize : ∀ data ∈ pieces, data.size + 33 < 65536)
    (hcount : pieces.length ≤ maxFragments) :
    openFragments chain (sealFragments chain pieces) = .ok (joinFragments pieces) := by
  have hfrag := chain.fragmented_protect chain.start pieces hne hsize
  have hlen : (chain.protect chain.start pieces).length ≤ maxFragments := by
    rw [chain.protect_length]; exact hcount
  simp [openFragments, sealFragments, decodeFragments_encode _ _ hfrag hlen, chain.check_protect]

/-- Soundness: a response that `openFragments` accepts is exactly the seal of some
    fragments, and the result is their data joined in order. -/
theorem openFragments_sound (chain : ChainedMac σ) (message data : ByteArray)
    (h : openFragments chain message = .ok data) :
    ∃ pieces, data = joinFragments pieces ∧ message = sealFragments chain pieces := by
  unfold openFragments at h
  split at h
  · contradiction
  rename_i version envelopes hdecode
  split at h
  · contradiction
  rename_i hversion
  split at h
  · contradiction
  rename_i pieces hcheck
  injection h with h
  subst h
  simp only [ne_eq, Decidable.not_not] at hversion
  subst hversion
  obtain ⟨hencode, _, _⟩ := decodeFragments_canonical _ _ _ hdecode
  refine ⟨pieces, rfl, ?_⟩
  rw [← hencode, chain.protect_of_check _ _ _ hcheck]
  rfl

/-- A response of one fragment with an independent tag is a single sealed frame. -/
theorem sealFragments_independent_single (mac : Mac) (message : ByteArray) :
    sealFragments (ChainedMac.independent mac) [message] = sealV3 mac message := by
  simp [sealFragments, ChainedMac.protect, ChainedMac.independent, sealV3, encodeFragments_single]

/-- The feed-forward chain starts with a plain tag, so a response of one fragment is a
    single sealed frame there too. -/
theorem sealFragments_feedForward_single (mac : Mac) (message : ByteArray) :
    sealFragments (ChainedMac.feedForward mac) [message] = sealV3 mac message := by
  simp [sealFragments, ChainedMac.protect, ChainedMac.feedForward, sealV3, encodeFragments_single,
    ByteArray.empty_append]

end LeanS7CommPlus
