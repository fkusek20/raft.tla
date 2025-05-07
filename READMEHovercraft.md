## HovercRaft Changes We Added to the Original Raft Spec

So, we started with that standard `raft.tla` file you provided. That file describes the normal Raft consensus algorithm. We wanted to change it to work more like the "HovercRaft" idea, which tries to make Raft handle large client data requests more efficiently.

**The Problem with Original Raft (Why Change?)**

In the original `raft.tla`:
*   The `ClientRequest` action happens when the Leader gets data (`v`) from a client.
*   The Leader puts that actual data `v` directly into its `log`.
*   The `AppendEntries` action sends log entries containing that actual data `v` to all Followers.
*   If `v` is big, the Leader has to send lots of big messages, which can be slow.

**The HovercRaft Idea We Implemented**

The main idea is to stop making the Leader responsible for sending the *big data* payload. Instead:
1.  **Payload Delivery:** The client sends the big data payload *separately* to *all* servers (Leader and Followers) using a "Switch".
2.  **Ordering:** The Leader just decides the *order* for these payloads and tells the Followers the order using a small *ID* (a `RequestID`) that refers to the payload.
3.  **Matching:** Followers receive the payload from the Switch and the ordering ID from the Leader and match them up before putting the entry (with the ID) in their log.

**What We ADDED to the Original `raft.tla`:**

1.  **New Things for Payloads & IDs:**
    *   `RequestID` (in `raftConstants`): A new type of value, basically just a unique name or number for each client request's payload.
    *   `SwitchRequest` (in `raftConstants`): A new type of message used by the "Switch" mechanism.
    *   `payloadMap` (in `raftVariables`, `raftInit`): A new **global variable**. Think of it like a shared dictionary or bulletin board where `payloadMap["some_request_id"]` stores the actual big data payload. Everyone can look data up here if they know the ID.
    *   `buffer` (in `raftVariables`, `raftInit`): A new **per-server variable**. Each server gets its own private `buffer`, which is just a set holding the `RequestID`s of payloads it has received from the "Switch" but hasn't yet matched with an order from the Leader.

2.  **New Actions for the "Switch":**
    *   `SwitchSend(payload_)` (in `raftActionsSolution`, added to `Next`): This simulates the client sending data *to the Switch*.
        *   It creates a new unique `RequestID` (`req`).
        *   It stores the actual `payload_` in the shared `payloadMap` (e.g., `payloadMap[req] = payload_`).
        *   It sends a *small* `SwitchRequest` message containing only the `reqId` to *everyone* (conceptually).
    *   `SwitchDeliver(s, msg)` (in `raftActionsSolution`, added to `Next`): This simulates a server `s` receiving a `SwitchRequest` message.
        *   It takes the `reqId` from the message.
        *   It adds this `reqId` to its own private `buffer[s]`. Now the server knows it has received the payload for this ID, even if it doesn't know the order yet.

3.  **New Way for Leader to Handle Requests:**
    *   We **removed** the original `ClientRequest` action from the `Next` definition in `raftSpec.tla`. The Leader doesn't directly take client data values anymore.
    *   `LeaderProposeRequest(i)` (in `raftActionsSolution`, added to `Next`): This is the Leader's *new* way to add something to the log.
        *   The Leader looks inside *its own* `buffer[i]` for a `RequestID` it received via `SwitchDeliver`.
        *   It picks one `reqId`.
        *   It creates a log entry like `[term |-> t, value |-> reqId]` -- notice the **`value` field now holds the ID**, not the actual data!
        *   It appends this new (small) entry to its `log[i]`.
        *   It removes the `reqId` from its `buffer[i]` (it has proposed it now).

**What We CHANGED in the Original `raft.tla`:**

1.  **Log Content:** The `log` variable now stores entries containing `RequestID`s in the `value` field, not the original `Value` payloads.

2.  **`AppendEntries` Action:**
    *   When the Leader prepares entries to send, it fetches entries like `[term |-> t, value |-> reqId]` from its log.
    *   The `mentries` field in the `AppendEntriesRequest` message now contains these *ID-based* entries. The messages are smaller!

3.  **`HandleAppendEntriesRequest` Action:** This had the biggest change for Followers:
    *   It still checks the term and previous log index (`logOk`).
    *   **Crucially:** Before accepting an entry `e = [term |-> t, value |-> reqId]` from the Leader, it **checks if `reqId` is in its own private `buffer[i]`**.
    *   If `reqId` **IS in the buffer**: This means the Follower got the payload separately from the Switch! It can now safely:
        *   Append the entry `e` (with the `reqId`) to its `log[i]`.
        *   **Remove `reqId` from its `buffer[i]`** (it's now matched and logged).
        *   Reply success to the Leader.
    *   If `reqId` **IS NOT in the buffer**: The Follower doesn't have the payload yet. It *cannot* append the entry. It must reply failure to the Leader.

4.  **`HandleAppendEntriesResponse` Action:** Minor change to make sure `matchIndex` doesn't go backward if messages arrive out of order (using `Max`).

**How it Works Now (Simplified Flow):**

1.  Client sends "BigData" via `SwitchSend`. ID `req123` is created, `payloadMap["req123"]` gets "BigData". `SwitchRequest` with `req123` goes out.
2.  Leader L, Follower F1, Follower F2 all run `SwitchDeliver` and add `req123` to their `buffer`.
3.  Leader L runs `LeaderProposeRequest`, picks `req123` from its buffer, puts `[term: 5, value: "req123"]` in its log, and clears `req123` from its buffer.
4.  Leader L sends `AppendEntries` to F1 with the entry `[term: 5, value: "req123"]`.
5.  F1 runs `HandleAppendEntriesRequest`. It checks its `buffer`. Does it have `req123`? Yes! So, it adds `[term: 5, value: "req123"]` to its log, removes `req123` from its buffer, and replies success.
6.  Leader eventually commits the entry. When F1 applies the committed entry, it sees the value is `"req123"`, looks up `payloadMap["req123"]` to get the actual "BigData", and uses that.

Basically, we separated the slow data transfer from the fast ordering mechanism of Raft!

Date added 25/04/2025 did not do commits before I forgot 

1.  **Modeled the "Switch":** I treated the Switch like a special, non-Raft server in my TLA+ spec, identifying it with a constant `switchIndex`.
2.  **Switch Stores Full Request:** I designed it so when a client sends a request (value `v`), the Switch stores the *entire thing*, including the payload, in its own log (`log[switchIndex]`). The entry I used looks like `[term |-> 0, value |-> v, payload |-> v]`.
3.  **Implemented `SwitchClientRequest(v)`:** I created this TLA+ action to simulate the client sending `v` *only* to the Switch. In the action, the Switch updates its log with the new entry and increments the `maxc` counter.
4.  **Tested in Isolation:** I set up a special test configuration (`MySpecSwitchTest` and `FakeMaxCInv`) in the TLA+ Toolbox. This setup was designed to *only* run my new `SwitchClientRequest` action and check if `maxc` was being incremented correctly against the `MaxClientRequests` limit.
5.  **Verified the Test:** I ran the model checker with this test setup. It successfully found the expected violation of `FakeMaxCInv`, which proves that my `SwitchClientRequest` action works correctly and increments `maxc` as required for this first step.

**In short:** I successfully modeled the client -> Switch interaction and proved that part works according to the specific instructions for this first stage. I haven't yet connected the Switch to the actual Raft leader or followers in the spec.

Date added 30/04/2025

## Goal

The main goal of this project is to modify a standard Raft TLA+ specification to implement the HovercRaft consensus algorithm variation, based on the design and requirements provided by the professor. HovercRaft aims to improve Raft's performance, especially for large client requests, by separating the ordering of requests from the delivery of the actual data payload.

## What I Did So Far (Implementation Steps)

Following the professor's design notes and examples, I made the following changes to the Raft TLA+ specs:

1.  **Modeled the Switch Component:**
    *   I designated one of the servers (using the identifier `"r1"` in the model configuration) to act as the non-Raft "Switch" component.
    *   I added a `Switch` state constant and assigned `state[r1]` to `Switch` in the initial configuration (`MyInit`).
    *   I defined a `Servers` constant (`{"r2", "r3", "r4"}`) to represent the actual Raft consensus group, excluding the Switch.

2.  **Added HovercRaft Variables:**
    *   `switchBuffer`: A variable where the Switch component (`r1`) stores the full client request details (`term`, `value`, `payload`) after the Leader acknowledges it.
    *   `unorderedRequests`: A buffer for *each* server (including the Switch) to store the `Value` (ID) of requests whose payloads have been received from the Switch but haven't been ordered/processed by Raft log replication yet.
    *   `switchSentRecord`: A record kept by the Switch to track which `<<Value, Term>>` pairs it has already sent to each Raft server, preventing redundant payload deliveries.

3.  **Implemented Core HovercRaft Actions:**
    *   `SwitchClientRequest(switchIndex, ldr, v)`: Simulates the client request `v` arriving. The *Leader* (`ldr`) tells the *Switch* (`switchIndex`) to store the full request details (using the Leader's current term) in `switchBuffer`. It also increments `maxc`.
    *   `SwitchClientRequestReplicate(switchIndex, raftSrv, val)`: The *Switch* picks a request ID (`val`) from its `switchBuffer` and replicates it to a specific Raft server (`raftSrv`). This adds `val` to `unorderedRequests[raftSrv]` and updates `switchSentRecord[raftSrv]`. (This models the payload delivery).
    *   `LeaderIngestHovercRaftRequest(ldr, val)`: The *Leader* (`ldr`) selects a request ID (`val`) known to be in `switchBuffer`. It creates a **metadata-only** entry (`[term |-> currentTerm, value |-> val]`) and appends it to its own Raft log (`log[ldr]`). It also removes `val` from its own `unorderedRequests[ldr]` buffer.

4.  **Modified Raft Actions:**
    *   `HandleAppendEntriesRequest(flw, ldr, m)`: Modified so that a *Follower* (`flw`) receiving a metadata entry (`[term, val]`) from the Leader (`ldr`) **must** check if `val` is present in its own `unorderedRequests[flw]` buffer. Only if the payload ID is present does it accept the metadata entry into its log (`log[flw]`) and remove the ID from `unorderedRequests[flw]`.
    *   `AppendEntries(ldr, flw)`: This now sends the *metadata-only* entries present in the leader's log.
    *   Standard Raft Actions (`Timeout`, `RequestVote`, `BecomeLeader`, `AdvanceCommitIndex`, etc.) and Invariants (`LogInv`, etc.) were scoped to operate only on the `Servers` set (excluding `switchIndex`).

5.  **Corrected Specification:**
    *   Fixed various TLA+ errors, including ensuring all new variables were correctly handled in `UNCHANGED` clauses for all actions, resolving parse errors related to `LET` vs `==`, and fixing quantifier issues (`\A`, `\E`) over sequences.

## Testing Strategy and Results

To verify the implementation stages, I followed the professor's guidance:

1.  **Test Setup:**
    *   Created a specific initial state `MyInit` based on the professor's example (r2 starts as Leader, r1 as Switch, etc.).
    *   Created a next-state relation `MySwitchNext` containing only the HovercRaft actions and the Raft actions needed for log replication and commit (i.e., no leader election actions).
    *   Defined the main specification for this test as `MySwitchSpec == MyInit /\ [][MySwitchNext]_vars`.
    *   Configured the TLA+ Toolbox constants (`Server`, `Servers`, `switchIndex`, `Value`, etc.) to match the example.

2.  **Test 1: Payload Replication to Buffers:**
    *   **Invariant Checked:** `AllServersHaveOneUnorderedRequestInv == \E s \in Servers : Cardinality(unorderedRequests[s]) /= Cardinality(Value)` (or `/= 2`). This invariant is designed to *fail* (be violated) only when *all* Raft servers have received *all* payloads (v1, v2) into their `unorderedRequests` buffer.
    *   **Result:** **SUCCESS!** The model checker ran `MySwitchSpec` and reported a violation of `AllServersHaveOneUnorderedRequestInv`. The error trace clearly showed the sequence: `SwitchClientRequest` populating `switchBuffer`, followed by `SwitchClientRequestReplicate` running enough times to add both "v1" and "v2" to the `unorderedRequests` buffers of r2, r3, and r4, at which point the invariant correctly became false.
    *   **Conclusion:** This confirms that the Switch mechanism for buffering requests and replicating their IDs/payloads to the Raft servers' local buffers is working as designed in the model.

## Next Steps

Now that I've confirmed the initial request handling and payload replication simulation is working, the next step is to **verify the end-to-end commit process**:

1.  **Run the same model configuration:** Use the TLA+ Toolbox with the `MySwitchSpec` behavior spec and the same constants.
2.  **Change Invariant:** Instead of checking `AllServersHaveOneUnorderedRequestInv`, I will **check the commit progress invariant**:
    ```tla
    NoRaftServerHasCommittedYet == \A srv \in Servers : commitIndex[srv] = 0
    ```
3.  **Expected Outcome:** I expect this `NoRaftServerHasCommittedYet` invariant to be **violated**. The error trace for this violation should show the full sequence: `SwitchClientRequest` -> `SwitchClientRequestReplicate` -> `LeaderIngestHovercRaftRequest` -> `AppendEntries` (metadata) -> `HandleAppendEntriesRequest` (follower logs metadata) -> `HandleAppendEntriesResponse` -> `AdvanceCommitIndex`. This will demonstrate that a request successfully went through the HovercRaft pipeline and was committed by the Raft consensus mechanism.
4.  **Check Raft Safety:** During this run, I will also keep the standard Raft safety invariants (`LogInv`, `LeaderCompletenessInv`, etc., scoped to `Servers`) checked to ensure the HovercRaft changes haven't broken core Raft guarantees.

Date 07/05/2025