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