# Informal Specification: Message Type Classification

**Source**: `src/raw_node.rs` (`is_local_msg`, `is_response_msg`) and `src/raft.rs` (`vote_resp_msg_type`)

---

## Purpose

The Raft implementation classifies protocol message types into semantic categories:

- **Local messages** — generated internally (not sent over the network to peers); they drive the local node's timer logic or reflect network-layer feedback.
- **Response messages** — replies produced by a follower/peer in response to a leader's request; used to filter out messages that cannot be relayed.
- **Vote response mapping** — given a vote-request type, compute the corresponding vote-response type.

These functions are used as guards when routing and filtering messages.

---

## `is_local_msg(t: MessageType) -> bool`

Returns `true` iff `t` is one of:

| Type | Numeric | Meaning |
|------|---------|---------|
| `MsgHup` | 0 | Election timeout — start a new election |
| `MsgBeat` | 1 | Heartbeat timeout — send heartbeats |
| `MsgUnreachable` | 10 | Application notifies: peer is unreachable |
| `MsgSnapStatus` | 11 | Application reports snapshot delivery status |
| `MsgCheckQuorum` | 12 | Periodic quorum-check trigger |

**Preconditions**: `t` is any valid `MessageType` value.

**Postcondition**: Returns `true` iff `t ∈ {MsgHup, MsgBeat, MsgUnreachable, MsgSnapStatus, MsgCheckQuorum}`.

---

## `is_response_msg(t: MessageType) -> bool` (private)

Returns `true` iff `t` is one of:

| Type | Numeric | Meaning |
|------|---------|---------|
| `MsgAppendResponse` | 4 | Reply to `MsgAppend` |
| `MsgRequestVoteResponse` | 6 | Reply to `MsgRequestVote` |
| `MsgHeartbeatResponse` | 9 | Reply to `MsgHeartbeat` |
| `MsgUnreachable` | 10 | Unreachability notice (also local) |
| `MsgRequestPreVoteResponse` | 18 | Reply to `MsgRequestPreVote` |

**Preconditions**: `t` is any valid `MessageType` value.

**Postcondition**: Returns `true` iff `t ∈ {MsgAppendResponse, MsgRequestVoteResponse, MsgHeartbeatResponse, MsgUnreachable, MsgRequestPreVoteResponse}`.

---

## `vote_resp_msg_type(t: MessageType) -> MessageType`

**Preconditions**: `t ∈ {MsgRequestVote, MsgRequestPreVote}`. Panics otherwise.

**Postconditions**:
- `vote_resp_msg_type(MsgRequestVote) = MsgRequestVoteResponse`
- `vote_resp_msg_type(MsgRequestPreVote) = MsgRequestPreVoteResponse`

---

## Key Properties

### P1 — is_local_msg is exactly the documented 5 types
```
isLocalMsg t ↔ t ∈ {MsgHup, MsgBeat, MsgUnreachable, MsgSnapStatus, MsgCheckQuorum}
```

### P2 — is_response_msg is exactly the documented 5 types
```
isResponseMsg t ↔ t ∈ {MsgAppendResponse, MsgRequestVoteResponse, MsgHeartbeatResponse,
                        MsgUnreachable, MsgRequestPreVoteResponse}
```

### P3 — Overlap: exactly MsgUnreachable is both local and response
```
(isLocalMsg t ∧ isResponseMsg t) ↔ t = MsgUnreachable
```
`MsgUnreachable` is an unusual type: it is generated locally by the application (so "local") but also classified as a "response" since it informs the leader's replication logic. This overlap is intentional.

### P4 — vote_resp_msg_type is a response message
```
∀ t ∈ {MsgRequestVote, MsgRequestPreVote}, isResponseMsg (voteRespMsgType t)
```

### P5 — vote_resp_msg_type is not a local message
```
∀ t ∈ {MsgRequestVote, MsgRequestPreVote}, ¬isLocalMsg (voteRespMsgType t)
```

### P6 — vote_resp_msg_type is involutive on its domain (paired with a left-inverse)
```
voteRespMsgType MsgRequestVote = MsgRequestVoteResponse
voteRespMsgType MsgRequestPreVote = MsgRequestPreVoteResponse
```

### P7 — Non-local messages: most common protocol messages are not local
```
∀ t ∈ {MsgPropose, MsgAppend, MsgRequestVote, MsgHeartbeat, ...}, ¬isLocalMsg t
```

---

## All MessageTypes (proto enum for reference)

```
MsgHup=0, MsgBeat=1, MsgPropose=2, MsgAppend=3, MsgAppendResponse=4,
MsgRequestVote=5, MsgRequestVoteResponse=6, MsgSnapshot=7, MsgHeartbeat=8,
MsgHeartbeatResponse=9, MsgUnreachable=10, MsgSnapStatus=11, MsgCheckQuorum=12,
MsgTransferLeader=13, MsgTimeoutNow=14, MsgReadIndex=15, MsgReadIndexResp=16,
MsgRequestPreVote=17, MsgRequestPreVoteResponse=18
```

---

## Inferred Intent

The three functions form a "message type algebra" that allows the Raft core to:
1. Identify messages that should never be sent over the wire (`is_local_msg`)
2. Identify messages that are replies (used to avoid re-routing responses as if they were new requests)
3. Unambiguously pair a vote request with its expected response type

The overlap of `MsgUnreachable` in both `is_local_msg` and `is_response_msg` is intentional: it is a special signal from the transport layer that is handled in both contexts.

---

## Open Questions

1. **Is the MsgUnreachable overlap intentional?** It appears in both `is_local_msg` and `is_response_msg`. This should be documented more explicitly.
2. **Completeness**: Are there message types that are neither local nor response? (Answer: yes — MsgPropose, MsgAppend, MsgRequestVote, MsgSnapshot, MsgHeartbeat, MsgTransferLeader, MsgTimeoutNow, MsgReadIndex, MsgReadIndexResp, MsgRequestPreVote.)
3. **Exhaustiveness of `vote_resp_msg_type`**: The function panics on non-vote inputs. Is this the right interface, or should it return `Option`?

---

*🔬 Lean Squad — automatically generated informal specification.*
