module ModelingTM {
    type ProcessId = nat
    type MemoryObject = nat
    type TimeStamp = nat

    class Operation {
        const isWrite: bool
        const memObject: MemoryObject
    }

    class Transaction {
        const ops: seq<Operation>
    }

    // Process state : transaction progress and process memory.
    class ProcessState {
        // currentTx : id of tx being processed. txs.size() means done.
        const currentTx: nat
        // currentOp :
        //      - tx.ops.size() represents tryCommit operation.
        //      - -1 represents abort operation
        //      - values in between represent read and write operations
        const currentOp: int
        // sub-operations of the operation, see the step function
        const currentSubOp: nat

        // Set of read objects with original observed timestamp.
        const readSet: map<MemoryObject, TimeStamp>
        // Set of written objects.
        const writeSet: set<MemoryObject>

        constructor () {
            currentTx := 0;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor nextSubOp(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp
            ensures this.currentSubOp == that.currentSubOp + 1
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp + 1;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor nextOp(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp + 1
            ensures this.currentSubOp == 0
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp + 1;
            currentSubOp := 0;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor abortTx(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == -1
            ensures this.currentSubOp == 0
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := -1;
            currentSubOp := 0;
            readSet := that.readSet;
            writeSet := that.writeSet;
        }

        constructor restartTx(that: ProcessState)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == 0
            ensures this.currentSubOp == 0
            ensures this.readSet == map[]
            ensures this.writeSet == {}
        {
            currentTx := that.currentTx;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor nextTx(that: ProcessState)
            ensures this.currentTx == that.currentTx + 1
            ensures this.currentOp == 0
            ensures this.currentSubOp == 0
            ensures this.readSet == map[]
            ensures this.writeSet == {}
        {
            currentTx := that.currentTx + 1;
            currentOp := 0;
            currentSubOp := 0;
            readSet := map[];
            writeSet := {};
        }

        constructor addToReadSet(that: ProcessState, obj: MemoryObject, ts: TimeStamp)
            ensures currentTx == that.currentTx
            ensures currentOp == that.currentOp
            ensures currentSubOp == that.currentSubOp
            ensures readSet.Keys == that.readSet.Keys + {obj}
                && readSet[obj] == ts
                && forall o :: o in readSet && o != obj ==> readSet[o] == that.readSet[o]
            ensures writeSet == that.writeSet
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp;
            readSet := that.readSet[obj := ts];
            writeSet := that.writeSet;
        }

        constructor addToWriteSet(that: ProcessState, obj: MemoryObject)
            ensures this.currentTx == that.currentTx
            ensures this.currentOp == that.currentOp
            ensures this.currentSubOp == that.currentSubOp
            ensures this.readSet == that.readSet
            ensures this.writeSet == that.writeSet + {obj}
        {
            currentTx := that.currentTx;
            currentOp := that.currentOp;
            currentSubOp := that.currentSubOp;
            readSet := that.readSet;
            writeSet := that.writeSet + {obj};
        }
    }

    class TMSystem {
        // Ordered list of transaction that each process should process
        const txQueues : map<ProcessId, seq<Transaction>>
        // State and memory of processes
        const procStates : map<ProcessId, ProcessState>
        // Dirty objects. (Replaces the object value in a real representation. Used for safety proof)
        const dirtyObjs: set<MemoryObject>
        // Object lock.
        const lockedObjs: set<MemoryObject>
        // Object timestamp. (Incremented at the end of any write transaction)
        const objTimeStamps: map<MemoryObject, nat>

        constructor (q: map<ProcessId, seq<Transaction>>) {
            txQueues := q;
            procStates := map[];
            dirtyObjs := {};
            lockedObjs := {};
            objTimeStamps := map[];
        }

        constructor initTimestamp(that: TMSystem, obj: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps.Keys ==  that.objTimeStamps.Keys + {obj}
                && objTimeStamps[obj] == 0
                && forall o :: o in objTimeStamps && o != obj ==> objTimeStamps[o] == that.objTimeStamps[o]
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps[obj := 0];
        }
        
        constructor updateState(that: TMSystem, pid: ProcessId, state: ProcessState)
            ensures txQueues == that.txQueues
            ensures procStates.Keys == that.procStates.Keys + {pid}
                && procStates[pid] == state
                && forall p :: p in procStates && p != pid ==> procStates[p] == that.procStates[p]
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates[pid := state];
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }
        
        constructor markDirty(that: TMSystem, obj: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs + {obj}
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs + {obj};
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }
        
        constructor clearDirty(that: TMSystem, writeSet: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs - writeSet
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs - writeSet;
            lockedObjs := that.lockedObjs;
            objTimeStamps := that.objTimeStamps;
        }

        constructor acquireLock(that: TMSystem, o: MemoryObject)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs + {o}
            ensures objTimeStamps == that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs + {o};
            objTimeStamps := that.objTimeStamps;
        }

        constructor releaseLocks(that: TMSystem, objs: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs - objs
            ensures objTimeStamps ==  that.objTimeStamps
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs - objs;
            objTimeStamps := that.objTimeStamps;
        }
        
        constructor updateTimestamps(that: TMSystem, objs: set<MemoryObject>)
            ensures txQueues == that.txQueues
            ensures procStates == that.procStates
            ensures dirtyObjs == that.dirtyObjs
            ensures lockedObjs == that.lockedObjs
            ensures objTimeStamps.Keys == that.objTimeStamps.Keys
                && forall o :: o in that.objTimeStamps ==>
                if(o in objs) then objTimeStamps[o] != that.objTimeStamps[o] else objTimeStamps[o] == that.objTimeStamps[o]
        {
            txQueues := that.txQueues;
            procStates := that.procStates;
            dirtyObjs := that.dirtyObjs;
            lockedObjs := that.lockedObjs;
            objTimeStamps := map o | o in that.objTimeStamps ::
                if(o in objs) then (that.objTimeStamps[o] + 1) else that.objTimeStamps[o];
        }

        predicate stateValid(pid: ProcessId, state: ProcessState)
            requires pid in procStates && state == procStates[pid]
        {
            && pid in txQueues
            && state.currentTx <= |txQueues[pid]|
            && if state.currentTx == |txQueues[pid]| then (
                // Queue finished
                && state.currentOp == 0
                && state.currentSubOp == 0
                && |state.readSet| == 0
                && |state.writeSet| == 0
            ) else if state.currentTx < |txQueues[pid]| then (
                // Queue unfinished
                && exists tx :: (
                    && tx == txQueues[pid][state.currentTx]
                    && state.currentOp <= |tx.ops|
                    && state.currentOp >= -1
                    && if (state.currentOp >= 0 && state.currentOp < |tx.ops|) then (
                        // Read/Write operations have at most two subOps
                        state.currentSubOp < 2
                    ) else if state.currentOp == |tx.ops| then (
                        // tryCommit has 4 subOps
                        state.currentSubOp < 4
                    ) else if state.currentOp == -1 then (
                        // abort has 3 subOps
                        state.currentSubOp < 3
                    ) else false
                )
                && state.readSet.Keys <= objTimeStamps.Keys
                && state.writeSet <= lockedObjs
            ) else false
        }

        predicate validSystem()
        {
            && procStates.Keys <= txQueues.Keys
            && dirtyObjs <= objTimeStamps.Keys
            && lockedObjs <= objTimeStamps.Keys
            && forall p, s :: p in procStates && s == procStates[p] ==> stateValid(p, s)
        }
    }
    

    method Step(input: TMSystem, pid: ProcessId) returns (system: TMSystem)
        requires pid in input.txQueues
        requires pid in input.procStates
        requires input.validSystem()
        ensures system.validSystem()
    {
        system := input;
        var state: ProcessState := system.procStates[pid];
        assert(system.stateValid(pid, state)); // Given by input.validSystem()
        var txs := system.txQueues[pid];

        if (state.currentTx >= |txs|) {
            // Nothing left to do.
            return;
        }
        var tx := txs[state.currentTx];
        
        if (state.currentOp == |tx.ops|) {
            // tryCommit
            if(state.currentSubOp == 0) {
                // Check locks
                if !(forall o :: o in state.readSet ==> o in state.writeSet || o !in system.lockedObjs) {
                    // Write detected (locked), aborting.
                    state := new ProcessState.abortTx(state);
                    system := new TMSystem.updateState(system, pid, state);
                    assume(system.validSystem()); // TODO : Remove assumption.
                    return;
                }
                // Continue to next sub-op.
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 1) {
                // Validate timestamps
                if !(forall o :: o in state.readSet ==> state.readSet[o] == system.objTimeStamps[o]) {
                    // Write detected (timestamp changed), aborting.
                    state := new ProcessState.abortTx(state);
                    system := new TMSystem.updateState(system, pid, state);
                    assume(system.validSystem()); // TODO : Remove assumption.
                    return;
                }
                // Can (and will) commit !
                // The writeset can now be read safely by others so we can remove the dirty mark.
                system := new TMSystem.clearDirty(system, state.writeSet);
                // Continue to next sub-op.
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 2) {
                // Update timestamps
                system := new TMSystem.updateTimestamps(system, state.writeSet);
                // Continue to next sub-op.
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 3) {
                // Release locks
                system := new TMSystem.releaseLocks(system, state.writeSet);
                // Commited. Continue to next transaction.
                state := new ProcessState.nextTx(state);
            } else {
                assert(false);
            }
        } else if (state.currentOp == -1) {
            // Abort
            if(state.currentSubOp == 0) {
                assert(state.currentTx < |system.txQueues[pid]|);
                // Restore written values (equivalent to removing dirty marks here).
                system := new TMSystem.clearDirty(system, state.writeSet);
                // Continue to next sub-op.
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 1) {
                // Update timestamps
                system := new TMSystem.updateTimestamps(system, state.writeSet);
                // Continue to next sub-op.
                state := new ProcessState.nextSubOp(state);
            } else if (state.currentSubOp == 2) {
                // Release locks
                system := new TMSystem.releaseLocks(system, state.writeSet);
                // Restart transaction.
                state := new ProcessState.restartTx(state);
            } else {
                assert(false);
            }
        } else if (state.currentOp >= 0 && state.currentOp < |tx.ops|) {
            // Read/Write op
            var op := tx.ops[state.currentOp];
            var o := op.memObject;
            
            // Init object timestamp if not present
            if(o !in system.objTimeStamps) {
                system := new TMSystem.initTimestamp(system, o);
            }
            assert(o in system.objTimeStamps);

            if(op.isWrite) {
                // Write
                if(state.currentSubOp == 0) {
                    if(!(op.memObject in state.writeSet)) {
                        // trylock
                        if(o in system.lockedObjs) {
                            // Failed locking, aborting.
                            state := new ProcessState.abortTx(state);
                        } else {
                            // Aquire lock. Continue to next sub-op.
                            system := new TMSystem.acquireLock(system, o);
                            state := new ProcessState.addToWriteSet(state, o);
                            state := new ProcessState.nextSubOp(state);
                        }
                    } else {
                        // Already in writeset, continue to next subOp.
                        state := new ProcessState.nextSubOp(state);
                    }
                } else if (state.currentSubOp == 1) {
                    // Do the write (equivalent to marking as dirty). Continue to next op.
                    system := new TMSystem.markDirty(system, o);
                    state := new ProcessState.nextOp(state);
                } else {
                    assert(false);
                }
            } else {
                // Read operation
                if(state.currentSubOp == 0) {
                    if(o in state.writeSet || o in state.readSet) {
                        // Already in writeSet or readSet, fast-skip to next op.
                        state := new ProcessState.nextOp(state);
                    } else {
                        // Read timestamp and add to readSet. Continue to next sub-op.
                        state := new ProcessState.addToReadSet(state, o, system.objTimeStamps[o]);
                        state := new ProcessState.nextSubOp(state);
                    }
                } else if (state.currentSubOp == 1) {
                    if(o in system.lockedObjs) {
                        // Object is locked, aborting.
                        state := new ProcessState.abortTx(state);
                    } else {
                        // All good. Continue to next op.
                        state := new ProcessState.nextOp(state);
                    }
                } else {
                    assert(false);
                }
            }
        } else {
            assert(false);
        }
        // Save the new state.
        system := new TMSystem.updateState(system, pid, state);
        assume(system.validSystem()); // TODO : Remove assumption.
    }
}

