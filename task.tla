/--------------------------------- MODULE task ---------------------------------

EXTENDS Integers, Sequences
VARIABLES inReady, inSuspended, inWaiting, inRunning, lastAction
TASK_COUNT == 3
MAX_COUNT_IN_READY == 3
PRIORITIES == 0..3
TYPES == {"basic", "extended"}
TASK == [type: TYPES,  priority: PRIORITIES]

Init ==
    /\ inSuspended \in [1..TASK_COUNT -> TASK]
    /\ inReady = [i \in PRIORITIES |-> <<>>]
    /\ inRunning = <<>>
    /\ inWaiting = <<>>
    /\ lastAction = "None"

currentReadyCount ==  Len(inReady[0])
                    + Len(inReady[1])
                    + Len(inReady[2])
                    + Len(inReady[3])

addToQueueReady(task) ==
    /\ currentReadyCount < MAX_COUNT_IN_READY
    /\ inReady' = [inReady EXCEPT ![task.priority] = Append(inReady[task.priority], task)]

removeFromSequenceByIndex(sequence, index) ==
    IF index <= Len(sequence)
    THEN SubSeq(sequence, 1, index - 1) \o SubSeq(sequence, index + 1, Len(sequence))
    ELSE sequence

preemptTask(deletedTask, preemptedTask) ==
    inReady' = [inReady EXCEPT
        ![deletedTask.priority] = Tail(inReady[deletedTask.priority]),
        ![preemptedTask.priority] = Append(inReady[preemptedTask.priority], preemptedTask)]

runTask(task) ==
    \/ /\ inRunning = <<>>
       /\ inReady' = [inReady EXCEPT ![task.priority] = SubSeq(inReady[task.priority], 2, Len(inReady[task.priority]))]
       /\ inRunning' = Append(inRunning, task)
    \/ /\ inRunning /= <<>>
       /\ preemptTask(task, inRunning[1])
       /\ inRunning' = <<task>>

\* suspended -> ready
activate ==
    \E i \in 1..Len(inSuspended):
        /\ inSuspended' = removeFromSequenceByIndex(inSuspended, i)
        /\ addToQueueReady(inSuspended[i])
        /\ UNCHANGED <<inRunning, inWaiting>>
        /\ lastAction' = "activate"

\* ready -> running
isExistsTaskToStart ==
    /\ currentReadyCount /= 0
    /\ \/ inRunning = <<>>
       \/ /\ inRunning /= <<>>
          /\ \E priority \in PRIORITIES:
                 /\ inReady[priority] /= <<>>
                 /\ inRunning[1].priority < priority

\* running -> ready
startAndPreempt ==
    /\ CASE
       (inReady[3] /= <<>>) -> runTask(inReady[3][1])
       [] (inReady[2] /= <<>>) -> runTask(inReady[2][1])
       [] (inReady[1] /= <<>>) -> runTask(inReady[1][1])
       [] (inReady[0] /= <<>>) -> runTask(inReady[0][1])
       [] OTHER -> FALSE
    /\ UNCHANGED <<inSuspended, inWaiting>>
    /\ lastAction' = "preempt"


\* running -> suspended
terminate ==
    /\ inRunning /= <<>>
    /\ inRunning' = <<>>
    /\ inSuspended' = inSuspended \o inRunning
    /\ UNCHANGED <<inReady, inWaiting>>
    /\ lastAction' = "terminate"

\* running -> waiting
wait ==
    /\ inRunning /= <<>>
    /\ inRunning[1].type = "extended"
    /\ inWaiting' = inWaiting \o inRunning
    /\ inRunning' = <<>>
    /\ UNCHANGED <<inReady, inSuspended>>
    /\ lastAction' = "wait"

\* waiting -> ready
release ==
    \E i \in 1..Len(inWaiting):
        /\ inWaiting' = removeFromSequenceByIndex(inWaiting, i)
        /\ addToQueueReady(inWaiting[i])
        /\ UNCHANGED <<inRunning, inSuspended>>
        /\ lastAction' = "release"

Inv1 == Len(inRunning) =< 1
Inv2 == currentReadyCount =< MAX_COUNT_IN_READY
Inv3 ==
        \/ Len(inRunning) = 0
        \/ lastAction = "release"
        \/ lastAction = "activate"
        \/ CASE
            (inReady[3] /= <<>> /\ inRunning[1].priority < 3) -> FALSE
            [] (inReady[2] /= <<>> /\ inRunning[1].priority < 2) -> FALSE
            [] (inReady[1] /= <<>> /\ inRunning[1].priority < 1) -> FALSE
            [] OTHER -> TRUE

Next ==
    \/ /\ isExistsTaskToStart /\ startAndPreempt
    \/ /\ ~isExistsTaskToStart /\
                    \/ activate
                    \/ terminate
                    \/ wait
                    \/ release

====