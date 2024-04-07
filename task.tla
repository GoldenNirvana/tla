/--------------------------------- MODULE task ---------------------------------

EXTENDS Integers, Sequences
VARIABLES inReady, inSuspended, inWaiting, inRunning
TASK_COUNT == 2
MAX_COUNT_IN_READY == 1
PRIORITIES == 0..3
TYPES == {"basic", "extended"}
TASK == [type: TYPES,  priority: PRIORITIES]

\* Изначально COUNT задач находятся в suspended, и 0 в остальных состояниях
Init ==
    /\ inSuspended \in [1..TASK_COUNT -> TASK]
    /\ inReady = [i \in PRIORITIES |-> <<>>]
    /\ inRunning = <<>>
    /\ inWaiting = <<>>

\* Всего задач в ready
currentReadyCount == Len(inReady[0]) + Len(inReady[1]) + Len(inReady[2]) + Len(inReady[3])

\* Удаление из очереди по индексу
removeFromSequenceByIndex(sequence, index) ==
    IF index <= Len(sequence)
    THEN SubSeq(sequence, 1, index - 1) \o SubSeq(sequence, index + 1, Len(sequence))
    ELSE sequence

\* Удаление из очереди
popFromSequence(task) ==
    /\ inReady' = [inReady EXCEPT ![task.priority] = SubSeq(inReady[task.priority], 2, Len(inReady[task.priority]))]

\* Добавление в очередь
addToQueueReady(task) ==
    /\ currentReadyCount < MAX_COUNT_IN_READY
    /\ inReady' = [inReady EXCEPT ![task.priority] = Append(inReady[task.priority], task)]

preeptTask(deletedTask, preemptedTask) ==
    inReady' = [inReady EXCEPT
        ![deletedTask.priority] = Tail(inReady[deletedTask.priority]),
        ![preemptedTask.priority] = Append(inReady[preemptedTask.priority], preemptedTask)]

\* ready -> running
runTask(task) ==
    \/ /\ inRunning = <<>>
       /\ popFromSequence(task)
       /\ Len(inReady[task.priority]) > 0
       /\ inRunning' = Append(inRunning, task)
    \/ /\ inRunning /= <<>>
       /\ preeptTask(task, inRunning[1])
       /\ inRunning' = <<task>>

\* suspended -> ready
activate ==
    \E i \in 1..Len(inSuspended):
        /\ inSuspended' = removeFromSequenceByIndex(inSuspended, i)
        /\ addToQueueReady(inSuspended[i])
        /\ UNCHANGED <<inRunning, inWaiting>>

\* Изменение выполняющейся задачи, реализация логики вытеснения низкоприоритетной задачи
start ==
    /\ currentReadyCount /= 0
    /\ \/ inRunning = <<>>
       \/ /\ inRunning /= <<>>
          /\ \E priority \in PRIORITIES:
                 /\ inReady[priority] /= <<>>
                 /\ inRunning[1].priority < priority

\* running - ready
preempt ==
    /\ CASE
       (inReady[3] /= <<>>) -> runTask(inReady[3][1])
       [] (inReady[2] /= <<>>) -> runTask(inReady[2][1])
       [] (inReady[1] /= <<>>) -> runTask(inReady[1][1])
       [] (inReady[0] /= <<>>) -> runTask(inReady[0][1])
       [] OTHER -> FALSE
    /\ UNCHANGED <<inSuspended, inWaiting>>

\* running -> suspended
terminate ==
    /\ inRunning /= <<>>
    /\ inRunning' = <<>>
    /\ inSuspended' = inSuspended \o inRunning
    /\ UNCHANGED <<inReady, inWaiting>>

\* running -> waiting
wait ==
    /\ inRunning /= <<>>
    /\ inRunning[1].type = "extended"
    /\ inWaiting' = inWaiting \o inRunning
    /\ inRunning' = <<>>
    /\ UNCHANGED <<inReady, inSuspended>>

\* waiting -> ready
release ==
    \E i \in 1..Len(inWaiting):
        /\ inWaiting' = removeFromSequenceByIndex(inWaiting, i)
        /\ addToQueueReady(inWaiting[i])
        /\ UNCHANGED <<inRunning, inSuspended>>

Properties ==
    /\ Len(inRunning) =< 1
    /\ currentReadyCount =< MAX_COUNT_IN_READY
    /\ (inRunning = <<>>)
    \/ /\ (inRunning /= <<>>)
       /\ CASE
          (inReady[3] /= <<>> /\ inRunning[1].priority < 3) -> TRUE
          [] (inReady[2] /= <<>> /\ inRunning[1].priority < 2) -> TRUE
          [] (inReady[1] /= <<>> /\ inRunning[1].priority < 1) -> TRUE
          [] OTHER -> TRUE

Next ==
    \/ /\ start
       /\ preempt
    \/ /\ ~start
       /\ \/ activate
          \/ terminate
          \/ wait
          \/ release
=============================================================================
