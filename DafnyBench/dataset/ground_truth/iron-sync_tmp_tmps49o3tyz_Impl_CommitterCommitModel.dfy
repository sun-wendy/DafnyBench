// include "IOModel.i.dfy"
// include "../lib/DataStructures/LinearMutableMap.i.dfy"

// module CommitterCommitModel {
//   import opened NativeTypes
//   import opened Options

//   import opened DiskLayout
//   import opened InterpretationDiskOps
//   import opened ViewOp
//   import JC = JournalCache
//   import opened Journal
//   import opened JournalBytes
//   import opened DiskOpModel
//   import SectorType

//   import LinearMutableMap
//   // import opened StateModel
//   import opened IOModel

//   function SyncReqs2to1Iterate(
//       m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>,
//       it: LinearMutableMap.Iterator<JC.SyncReqStatus>,
//       m0: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//     : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   requires LinearMutableMap.WFIter(m, it)
//   requires LinearMutableMap.Inv(m0)
//   requires m0.contents.Keys == it.s
//   ensures LinearMutableMap.Inv(m')
//   decreases it.decreaser
//   {
//     if it.next.Done? then
//       m0
//     else (
//       LinearMutableMap.LemmaIterIndexLtCount(m, it);
//       LinearMutableMap.CountBound(m);
//       SyncReqs2to1Iterate(
//         m,
//         LinearMutableMap.IterInc(m, it),
//         LinearMutableMap.Insert(m0, it.next.key,
//             (if it.next.value == JC.State2 then JC.State1 else it.next.value))
//       )
//     )
//   }

//   function {:opaque} SyncReqs2to1(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//       : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   ensures LinearMutableMap.Inv(m')
//   {
//     SyncReqs2to1Iterate(m,
//       LinearMutableMap.IterStart(m),
//       LinearMutableMap.Constructor(128))
//   }

//   lemma SyncReqs2to1Correct(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   ensures SyncReqs2to1(m).contents == JC.syncReqs2to1(m.contents)
//   {
//     reveal_SyncReqs2to1();
//     var it := LinearMutableMap.IterStart(m);
//     var m0 := LinearMutableMap.Constructor(128);
//     while !it.next.Done?
//     invariant LinearMutableMap.Inv(m)
//     invariant LinearMutableMap.WFIter(m, it)
//     invariant LinearMutableMap.Inv(m0)
//     invariant m0.contents.Keys == it.s
//     invariant forall id | id in it.s ::
//         m0.contents[id] == (if m.contents[id] == JC.State2 then JC.State1 else m.contents[id])
//     invariant SyncReqs2to1(m) == SyncReqs2to1Iterate(m, it, m0)
//     decreases it.decreaser
//     {
//       LinearMutableMap.LemmaIterIndexLtCount(m, it);
//       LinearMutableMap.CountBound(m);
//       m0 := LinearMutableMap.Insert(m0, it.next.key,
//           (if it.next.value == JC.State2 then JC.State1 else it.next.value));
//       it := LinearMutableMap.IterInc(m, it);
//     }
//   }

//   function SyncReqs3to2Iterate(
//       m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>,
//       it: LinearMutableMap.Iterator<JC.SyncReqStatus>,
//       m0: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//     : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   requires LinearMutableMap.WFIter(m, it)
//   requires LinearMutableMap.Inv(m0)
//   requires m0.contents.Keys == it.s
//   ensures LinearMutableMap.Inv(m')
//   decreases it.decreaser
//   {
//     if it.next.Done? then
//       m0
//     else (
//       LinearMutableMap.LemmaIterIndexLtCount(m, it);
//       LinearMutableMap.CountBound(m);
//       SyncReqs3to2Iterate(
//         m,
//         LinearMutableMap.IterInc(m, it),
//         LinearMutableMap.Insert(m0, it.next.key,
//             (if it.next.value == JC.State3 then JC.State2 else it.next.value))
//       )
//     )
//   }

//   function {:opaque} SyncReqs3to2(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//       : (m' : LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   ensures LinearMutableMap.Inv(m')
//   {
//     SyncReqs3to2Iterate(m,
//       LinearMutableMap.IterStart(m),
//       LinearMutableMap.Constructor(128))
//   }

//   lemma SyncReqs3to2Correct(m: LinearMutableMap.LinearHashMap<JC.SyncReqStatus>)
//   requires LinearMutableMap.Inv(m)
//   ensures SyncReqs3to2(m).contents == JC.syncReqs3to2(m.contents)
//   {
//     reveal_SyncReqs3to2();
//     var it := LinearMutableMap.IterStart(m);
//     var m0 := LinearMutableMap.Constructor(128);
//     while !it.next.Done?
//     invariant LinearMutableMap.Inv(m)
//     invariant LinearMutableMap.WFIter(m, it)
//     invariant LinearMutableMap.Inv(m0)
//     invariant m0.contents.Keys == it.s
//     invariant forall id | id in it.s ::
//         m0.contents[id] == (if m.contents[id] == JC.State3 then JC.State2 else m.contents[id])
//     invariant SyncReqs3to2(m) == SyncReqs3to2Iterate(m, it, m0)
//     decreases it.decreaser
//     {
//       LinearMutableMap.LemmaIterIndexLtCount(m, it);
//       LinearMutableMap.CountBound(m);
//       m0 := LinearMutableMap.Insert(m0, it.next.key,
//           (if it.next.value == JC.State3 then JC.State2 else it.next.value));
//       it := LinearMutableMap.IterInc(m, it);
//     }
//   }

  // function {:opaque} WriteOutJournal(cm: CM, io: IO)
  //     : (res : (CM, IO))
  // requires io.IOInit?
  // requires CommitterModel.WF(cm)
  // requires JournalistModel.I(cm.journalist).inMemoryJournalFrozen != []
  //       || JournalistModel.I(cm.journalist).inMemoryJournal != []
  // {
  //   var writtenJournalLen :=
  //       JournalistModel.getWrittenJournalLen(cm.journalist);

  //   var doingFrozen :=
  //     JournalistModel.hasFrozenJournal(cm.journalist);

  //   var (journalist', j) :=
  //     if doingFrozen then
  //       JournalistModel.packageFrozenJournal(cm.journalist)
  //     else
  //       JournalistModel.packageInMemoryJournal(cm.journalist);

  //   var start := start_pos_add(
  //       cm.superblock.journalStart,
  //       writtenJournalLen);

  //   var len := |j| as uint64 / 4096;

  //   var contiguous := start + len <= NumJournalBlocks();

  //   var io' := if contiguous then
  //     IOReqWrite(io.id, D.ReqWrite(JournalPoint(start), j))
  //   else (
  //     var cut := (NumJournalBlocks() - start) * 4096;
  //     IOReqWrite2(io.id, io.id2,
  //         D.ReqWrite(JournalPoint(start), j[..cut]),
  //         D.ReqWrite(JournalPoint(0), j[cut..]))
  //   );

  //   var outstandingJournalWrites' := if contiguous
  //       then cm.outstandingJournalWrites + {io.id}
  //       else cm.outstandingJournalWrites + {io.id, io.id2};

  //   var frozenJournalPosition' := if doingFrozen
  //     then JournalistModel.getWrittenJournalLen(journalist')
  //     else cm.frozenJournalPosition;

  //   var syncReqs' := if doingFrozen
  //     then cm.syncReqs
  //     else SyncReqs3to2(cm.syncReqs);

  //   var cm' := cm
  //     .(outstandingJournalWrites := outstandingJournalWrites')
  //     .(journalist := journalist')
  //     .(frozenJournalPosition := frozenJournalPosition')
  //     .(syncReqs := syncReqs');

  //   (cm', io')
  // }

  // lemma WriteOutJournalCorrect(cm: CM, io: IO)
  // requires WriteOutJournal.requires(cm, io)
  // requires cm.superblockWrite.None?
  // ensures var (cm', io') := WriteOutJournal(cm, io);
  //   && CommitterModel.WF(cm')
  //   && ValidDiskOp(diskOp(io'))
  //   && IDiskOp(diskOp(io')).bdop.NoDiskOp?
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {
  //   var (cm', io') := WriteOutJournal(cm, io);
  //   reveal_WriteOutJournal();

  //   var writtenJournalLen :=
  //       JournalistModel.getWrittenJournalLen(cm.journalist);

  //   var doingFrozen :=
  //     JournalistModel.hasFrozenJournal(cm.journalist);

  //   var (journalist', j) :=
  //     if doingFrozen then
  //       JournalistModel.packageFrozenJournal(cm.journalist)
  //     else
  //       JournalistModel.packageInMemoryJournal(cm.journalist);

  //   var start := start_pos_add(
  //       cm.superblock.journalStart,
  //       writtenJournalLen);

  //   var jr := JournalRangeOfByteSeq(j).value;
  //   var len := |j| as uint64 / 4096;
  //   var contiguous := start + len <= NumJournalBlocks();

  //   assert |jr| == len as int;

  //   if contiguous {
  //     assert LocOfReqWrite(diskOp(io').reqWrite)
  //         == JournalRangeLocation(start, len);
  //     assert ValidDiskOp(diskOp(io'));
  //   } else {
  //     assert LocOfReqWrite(diskOp(io').reqWrite1)
  //         == JournalRangeLocation(start, NumJournalBlocks() - start);
  //     assert LocOfReqWrite(diskOp(io').reqWrite2)
  //         == JournalRangeLocation(0, len - (NumJournalBlocks() - start));
  //     JournalBytesSplit(j, len as int,
  //         NumJournalBlocks() as int - start as int);
  //     assert ValidDiskOp(diskOp(io'));
  //   }

  //   SyncReqs3to2Correct(cm.syncReqs);

  //   assert JC.WriteBackJournalReq(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp,
  //       jr);
  //   assert JC.NextStep(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp,
  //       JC.WriteBackJournalReqStep(jr));
  // }

  // predicate writeOutSuperblockAdvanceLog(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires io.IOInit?
  // requires CommitterModel.WF(cm)
  // {
  //   var writtenJournalLen :=
  //       JournalistModel.getWrittenJournalLen(cm.journalist);
  //   var newSuperblock := SectorType.Superblock(
  //     JC.IncrementSuperblockCounter(cm.superblock.counter),
  //     cm.superblock.journalStart,
  //     writtenJournalLen,
  //     cm.superblock.indirectionTableLoc
  //   );

  //   var loc := if cm.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();

  //   && cm'.superblockWrite.Some?
  //   && var id := cm'.superblockWrite.value;

  //   && RequestWrite(io, loc, SSM.SectorSuperblock(newSuperblock),
  //       id, io')
  //   && cm' == cm
  //     .(newSuperblock := Some(newSuperblock))
  //     .(superblockWrite := Some(id))
  //     .(commitStatus := JC.CommitAdvanceLog)
  // }

  // lemma writeOutSuperblockAdvanceLogCorrect(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires io.IOInit?
  // requires CommitterModel.WF(cm)
  // requires writeOutSuperblockAdvanceLog(cm, io, cm', io')
  // requires cm.status == StatusReady
  // requires cm.commitStatus.CommitNone?
  // requires cm.outstandingJournalWrites == {}
  // requires JournalistModel.I(cm.journalist).inMemoryJournalFrozen == []
  // ensures CommitterModel.WF(cm')
  // ensures ValidDiskOp(diskOp(io'))
  // ensures IDiskOp(diskOp(io')).bdop.NoDiskOp?
  // ensures JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {
  //   var writtenJournalLen :=
  //       JournalistModel.getWrittenJournalLen(cm.journalist);
  //   var newSuperblock := SectorType.Superblock(
  //     JC.IncrementSuperblockCounter(cm.superblock.counter),
  //     cm.superblock.journalStart,
  //     writtenJournalLen,
  //     cm.superblock.indirectionTableLoc
  //   );
  //   assert JC.WFSuperblock(newSuperblock);

  //   var loc := if cm.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();

  //   var id := cm'.superblockWrite.value;

  //   RequestWriteCorrect(io, loc, SSM.SectorSuperblock(newSuperblock),
  //       id, io');

  //   assert ValidDiskOp(diskOp(io'));

  //   assert JC.WriteBackSuperblockReq_AdvanceLog(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp);
  //   assert JC.NextStep(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp,
  //       JC.WriteBackSuperblockReq_AdvanceLog_Step);
  // }

  // predicate {:opaque} writeOutSuperblockAdvanceLocation(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires io.IOInit?
  // requires CommitterModel.Inv(cm)
  // requires cm.status == StatusReady
  // requires cm.frozenLoc.Some?
  // {
  //   var writtenJournalLen :=
  //       JournalistModel.getWrittenJournalLen(cm.journalist);
  //   var newSuperblock := SectorType.Superblock(
  //     JC.IncrementSuperblockCounter(cm.superblock.counter),
  //     start_pos_add(
  //         cm.superblock.journalStart,
  //         cm.frozenJournalPosition),
  //     writtenJournalLen - cm.frozenJournalPosition,
  //     cm.frozenLoc.value
  //   );

  //   var loc := if cm.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();

  //   && cm'.superblockWrite.Some?
  //   && var id := cm'.superblockWrite.value;

  //   && RequestWrite(io, loc, SSM.SectorSuperblock(newSuperblock),
  //       id, io')
  //   && cm' == cm
  //     .(newSuperblock := Some(newSuperblock))
  //     .(superblockWrite := Some(id))
  //     .(commitStatus := JC.CommitAdvanceLocation)
  // }

  // lemma writeOutSuperblockAdvanceLocationCorrect(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires io.IOInit?
  // requires CommitterModel.Inv(cm)
  // requires cm.status == StatusReady
  // requires cm.frozenLoc.Some?
  // requires cm.commitStatus.CommitNone?
  // requires cm.outstandingJournalWrites == {}
  // requires writeOutSuperblockAdvanceLocation(cm, io, cm', io')
  // requires JournalistModel.I(cm.journalist).inMemoryJournalFrozen == []
  // ensures CommitterModel.WF(cm')
  // ensures ValidDiskOp(diskOp(io'))
  // ensures IDiskOp(diskOp(io')).bdop.NoDiskOp?
  // ensures JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {
  //   reveal_writeOutSuperblockAdvanceLocation();

  //   var writtenJournalLen :=
  //       JournalistModel.getWrittenJournalLen(cm.journalist);
  //   var newSuperblock := SectorType.Superblock(
  //     JC.IncrementSuperblockCounter(cm.superblock.counter),
  //     start_pos_add(
  //         cm.superblock.journalStart,
  //         cm.frozenJournalPosition) as uint64,
  //     (writtenJournalLen - cm.frozenJournalPosition) as uint64,
  //     cm.frozenLoc.value
  //   );
  //   assert JC.WFSuperblock(newSuperblock);

  //   var loc := if cm.whichSuperblock == 0 then Superblock2Location() else Superblock1Location();

  //   var id := cm'.superblockWrite.value;

  //   RequestWriteCorrect(io, loc, SSM.SectorSuperblock(newSuperblock),
  //       id, io');

  //   assert ValidDiskOp(diskOp(io'));

  //   assert JC.WriteBackSuperblockReq_AdvanceLocation(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp);
  //   assert JC.NextStep(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp,
  //       JC.WriteBackSuperblockReq_AdvanceLocation_Step);
  // }

  // function {:opaque} freeze(cm: CM) : (cm': CM)
  // requires CommitterModel.WF(cm)
  // {
  //   var writtenJournalLen :=
  //       JournalistModel.getWrittenJournalLen(cm.journalist);
  //   cm.(frozenLoc := None)
  //     .(journalist := JournalistModel.freeze(cm.journalist))
  //     .(frozenJournalPosition := writtenJournalLen)
  //     .(isFrozen := true)
  //     .(syncReqs := SyncReqs3to2(cm.syncReqs))
  // }

  // lemma freezeCorrect(cm: CM)
  // requires CommitterModel.WF(cm)
  // requires cm.superblockWrite.None?

  // // Mostly we'll probably just do this with cm.frozenLoc == None
  // // but more generally we can do it whenever we have:
  // requires cm.status == StatusReady
  // requires cm.frozenLoc != Some(cm.superblock.indirectionTableLoc)
  // requires JournalistModel.I(cm.journalist).replayJournal == []

  // ensures var cm' := freeze(cm);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       FreezeOp)
  // {
  //   reveal_freeze();
  //   var cm' := freeze(cm);
  //   SyncReqs3to2Correct(cm.syncReqs);

  //   assert JC.Freeze(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       FreezeOp);
  //   assert JC.NextStep(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       FreezeOp,
  //       JC.FreezeStep);
  // }

  // function {:opaque} receiveFrozenLoc(
  //     cm: CM, loc: Location) : (cm': CM)
  // {
  //   cm.(frozenLoc := Some(loc))
  // }

  // lemma receiveFrozenLocCorrect(cm: CM, loc: Location)
  // requires CommitterModel.WF(cm)
  // requires cm.status == StatusReady
  // requires cm.isFrozen
  // requires !cm.frozenLoc.Some?
  // requires ValidIndirectionTableLocation(loc)

  // ensures var cm' := receiveFrozenLoc(cm, loc);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       SendFrozenLocOp(loc))
  // {
  //   reveal_receiveFrozenLoc();
  //   var cm' := receiveFrozenLoc(cm, loc);
  //   assert JC.ReceiveFrozenLoc(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       SendFrozenLocOp(loc));
  //   assert JC.NextStep(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       SendFrozenLocOp(loc),
  //       JC.ReceiveFrozenLocStep);
  // }

  // // == pushSync ==

  // function {:opaque} freeId<A>(syncReqs: LinearMutableMap.LinearHashMap<A>) : (id: uint64)
  // requires LinearMutableMap.Inv(syncReqs)
  // ensures id != 0 ==> id !in syncReqs.contents
  // {
  //   var maxId := LinearMutableMap.MaxKey(syncReqs);
  //   if maxId == 0xffff_ffff_ffff_ffff then (
  //     0
  //   ) else (
  //     maxId + 1
  //   )
  // }

  // function pushSync(cm: CM) : (CM, uint64)
  // requires CommitterModel.WF(cm)
  // {
  //   var id := freeId(cm.syncReqs);
  //   if id == 0 || cm.syncReqs.count as int >= 0x1_0000_0000_0000_0000 / 8 then (
  //     (cm, 0)
  //   ) else (
  //     var cm' := cm.(syncReqs := LinearMutableMap.Insert(cm.syncReqs, id, JC.State3));
  //     (cm', id)
  //   )
  // }

  // lemma pushSyncCorrect(cm: CM)
  // requires CommitterModel.WF(cm)

  // ensures var (cm', id) := pushSync(cm);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       if id == 0 then JournalInternalOp else PushSyncOp(id as int))
  // {
  //   var (cm', id) := pushSync(cm);
  //   if id == 0 || cm.syncReqs.count as int >= 0x1_0000_0000_0000_0000 / 8 {
  //     assert JC.NoOp(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         JournalDisk.NoDiskOp,
  //         JournalInternalOp);
  //     assert JC.NextStep(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         JournalDisk.NoDiskOp,
  //         JournalInternalOp,
  //         JC.NoOpStep);
  //   } else {
  //     assert JC.PushSyncReq(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         JournalDisk.NoDiskOp,
  //         PushSyncOp(id as int), id);
  //     assert JC.NextStep(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         JournalDisk.NoDiskOp,
  //         PushSyncOp(id as int),
  //         JC.PushSyncReqStep(id));
  //   }
  // }

  // // == popSync ==

  // function {:opaque} popSync(cm: CM, id: uint64) : (cm' : CM)
  // requires CommitterModel.WF(cm)
  // {
  //   cm.(syncReqs := LinearMutableMap.Remove(cm.syncReqs, id))
  // }

  // lemma popSyncCorrect(cm: CM, id: uint64)
  // requires CommitterModel.WF(cm)
  // requires id in cm.syncReqs.contents
  // requires cm.syncReqs.contents[id] == JC.State1
  // ensures var cm' := popSync(cm, id);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       PopSyncOp(id as int))
  // {
  //   var cm' := popSync(cm, id);
  //   reveal_popSync();
  //   assert JC.PopSyncReq(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       PopSyncOp(id as int), id);
  //   assert JC.NextStep(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       JournalDisk.NoDiskOp,
  //       PopSyncOp(id as int),
  //       JC.PopSyncReqStep(id));
  // }

  // // == AdvanceLog ==

  // predicate {:opaque} tryAdvanceLog(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires CommitterModel.WF(cm)
  // requires io.IOInit?
  // {
  //   var hasFrozen := JournalistModel.hasFrozenJournal(cm.journalist);
  //   var hasInMem := JournalistModel.hasInMemoryJournal(cm.journalist);
  //   if cm.superblockWrite.None? then (
  //     if hasFrozen || hasInMem then (
  //       (cm', io') == WriteOutJournal(cm, io)
  //     ) else if cm.outstandingJournalWrites == {} then (
  //       writeOutSuperblockAdvanceLog(cm, io, cm', io')
  //     ) else (
  //       && cm' == cm
  //       && io' == io
  //     )
  //   ) else (
  //     && cm' == cm
  //     && io' == io
  //   )
  // }

  // lemma tryAdvanceLogCorrect(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires CommitterModel.Inv(cm)
  // requires io.IOInit?
  // requires cm.status.StatusReady?
  // requires tryAdvanceLog(cm, io, cm', io')
  // ensures CommitterModel.WF(cm')
  // ensures ValidDiskOp(diskOp(io'))
  // ensures IDiskOp(diskOp(io')).bdop.NoDiskOp?
  // ensures JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {
  //   reveal_tryAdvanceLog();
  //   var hasFrozen := JournalistModel.hasFrozenJournal(cm.journalist);
  //   var hasInMem := JournalistModel.hasInMemoryJournal(cm.journalist);
  //   if cm.superblockWrite.None? {
  //     if hasFrozen || hasInMem {
  //       WriteOutJournalCorrect(cm, io);
  //     } else if (cm.outstandingJournalWrites == {}) {
  //       writeOutSuperblockAdvanceLogCorrect(cm, io, cm', io');
  //     } else {
  //       assert JC.NoOp( CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp, JournalInternalOp);
  //       assert JC.NextStep( CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
  //     }
  //   } else {
  //     assert JC.NoOp( CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp, JournalInternalOp);
  //     assert JC.NextStep( CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
  //   }
  // }

  // predicate {:opaque} tryAdvanceLocation(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires CommitterModel.Inv(cm)
  // requires io.IOInit?
  // requires cm.status == StatusReady
  // requires cm.frozenLoc.Some?
  // {
  //   var hasFrozen := JournalistModel.hasFrozenJournal(cm.journalist);
  //   var hasInMem := JournalistModel.hasInMemoryJournal(cm.journalist);
  //   if cm.superblockWrite.None? then (
  //     if hasFrozen || hasInMem then (
  //       (cm', io') == WriteOutJournal(cm, io)
  //     ) else if cm.outstandingJournalWrites == {} then (
  //       writeOutSuperblockAdvanceLocation(cm, io, cm', io')
  //     ) else (
  //       && cm' == cm
  //       && io' == io
  //     )
  //   ) else (
  //     && cm' == cm
  //     && io' == io
  //   )
  // }

  // lemma tryAdvanceLocationCorrect(cm: CM, io: IO,
  //     cm': CM, io': IO)
  // requires CommitterModel.Inv(cm)
  // requires io.IOInit?
  // requires cm.status.StatusReady?
  // requires cm.frozenLoc.Some?
  // requires tryAdvanceLocation(cm, io, cm', io')
  // ensures CommitterModel.WF(cm')
  // ensures ValidDiskOp(diskOp(io'))
  // ensures IDiskOp(diskOp(io')).bdop.NoDiskOp?
  // ensures JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io')).jdop,
  //       JournalInternalOp)
  // {
  //   reveal_tryAdvanceLocation();
  //   var hasFrozen := JournalistModel.hasFrozenJournal(cm.journalist);
  //   var hasInMem := JournalistModel.hasInMemoryJournal(cm.journalist);
  //   if cm.superblockWrite.None? {
  //     if hasFrozen || hasInMem {
  //       WriteOutJournalCorrect(cm, io);
  //     } else if (cm.outstandingJournalWrites == {}) {
  //       writeOutSuperblockAdvanceLocationCorrect(cm, io, cm', io');
  //     } else {
  //       assert JC.NoOp( CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp, JournalInternalOp);
  //       assert JC.NextStep( CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
  //     }
  //   } else {
  //     assert JC.NoOp( CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp, JournalInternalOp);
  //     assert JC.NextStep( CommitterModel.I(cm), CommitterModel.I(cm'), JournalDisk.NoDiskOp, JournalInternalOp, JC.NoOpStep);
  //   }
  // }

  // function {:opaque} writeBackSuperblockResp(
  //     cm: CommitterModel.CM) : CommitterModel.CM
  // requires CommitterModel.Inv(cm)
  // {
  //   if cm.status.StatusReady? &&
  //       cm.commitStatus.CommitAdvanceLocation? then (
  //     cm.(superblockWrite := None)
  //       .(superblock := cm.newSuperblock.value)
  //       .(newSuperblock := None)
  //       .(whichSuperblock := if cm.whichSuperblock == 0 then 1 else 0)
  //       .(syncReqs := SyncReqs2to1(cm.syncReqs))
  //       .(journalist :=
  //           JournalistModel.updateWrittenJournalLen(
  //             cm.journalist,
  //             JournalistModel.getWrittenJournalLen(cm.journalist)
  //               - cm.frozenJournalPosition
  //           )
  //        )
  //       .(frozenJournalPosition := 0)
  //       .(frozenLoc := None)
  //       .(isFrozen := false)
  //       .(commitStatus := JC.CommitNone)
  //   )
  //   else if cm.status.StatusReady? &&
  //       cm.commitStatus.CommitAdvanceLog? then (
  //     cm.(superblockWrite := None)
  //       .(superblock := cm.newSuperblock.value)
  //       .(newSuperblock := None)
  //       .(whichSuperblock := if cm.whichSuperblock == 0 then 1 else 0)
  //       .(syncReqs := SyncReqs2to1(cm.syncReqs))
  //       .(commitStatus := JC.CommitNone)
  //   )
  //   else (
  //     cm
  //   )
  // }

  // lemma writeBackSuperblockRespCorrect(
  //     cm: CommitterModel.CM, io: IO)
  // requires CommitterModel.Inv(cm)
  // requires ValidDiskOp(diskOp(io))
  // requires IDiskOp(diskOp(io)).jdop.RespWriteSuperblockOp?
  // requires Some(io.id) == cm.superblockWrite
  // ensures var cm' := writeBackSuperblockResp(cm);
  //   && CommitterModel.WF(cm')
  //   && JC.Next(
  //       CommitterModel.I(cm),
  //       CommitterModel.I(cm'),
  //       IDiskOp(diskOp(io)).jdop,
  //       if cm.status.StatusReady? && cm.commitStatus.CommitAdvanceLocation? then CleanUpOp else JournalInternalOp
  //   )
  // {
  //   reveal_writeBackSuperblockResp();
  //   var cm' := writeBackSuperblockResp(cm);
  //   SyncReqs2to1Correct(cm.syncReqs);
  //   if cm.status.StatusReady? &&
  //       cm.commitStatus.CommitAdvanceLocation? {
  //     assert JC.WriteBackSuperblockResp(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         IDiskOp(diskOp(io)).jdop,
  //         CleanUpOp);
  //     assert JC.NextStep(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         IDiskOp(diskOp(io)).jdop,
  //         CleanUpOp,
  //         JC.WriteBackSuperblockRespStep);
  //   }
  //   else if cm.status.StatusReady? &&
  //       cm.commitStatus.CommitAdvanceLog? {
  //     assert JC.WriteBackSuperblockResp(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         IDiskOp(diskOp(io)).jdop,
  //         JournalInternalOp);
  //     assert JC.NextStep(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         IDiskOp(diskOp(io)).jdop,
  //         JournalInternalOp,
  //         JC.WriteBackSuperblockRespStep);
  //   }
  //   else {
  //     assert JC.NoOp(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         IDiskOp(diskOp(io)).jdop,
  //         JournalInternalOp);
  //     assert JC.NextStep(
  //         CommitterModel.I(cm),
  //         CommitterModel.I(cm'),
  //         IDiskOp(diskOp(io)).jdop,
  //         JournalInternalOp,
  //         JC.NoOpStep);
  //   }
  // }
// }

