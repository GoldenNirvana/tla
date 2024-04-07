/--------------------------------- MODULE task ---------------------------------

EXTENDS Integers, Sequences
VARIABLES inReady, inSuspended, inWaiting, inRunning
COUNT == 1
COUNT_IN_READY == 1
PRIORITIES == 0..3
TYPES == { "basic", "extended" }
TASK == [ type: TYPES,  priority: PRIORITIES]

\* Изначально COUNT задач находятся в suspended, и 0 в остальных состояниях
Init ==
    /\ inSuspended \in [1..COUNT -> TASK]
    /\ inReady = [i \in PRIORITIES |-> <<>>]
    /\ inRunning = <<>>
    /\ inWaiting = <<>>

\* Всего задач в ready
CurrentReadyCount == Len(inReady[0]) + Len(inReady[1]) + Len(inReady[2]) + Len(inReady[3])

\* Удаление из очереди по индексу
RemoveFromSequenceByIndex(sequence, index) ==
    IF index <= Len(sequence)
    THEN SubSeq(sequence, 1, index - 1) \o SubSeq(sequence, index + 1, Len(sequence))
    ELSE sequence

\* Удаление из очереди
PopFromSequence(task) ==
    /\ inReady' = [inReady EXCEPT ![task.priority] = SubSeq(inReady[task.priority], 2, Len(inReady[task.priority]))]

\* Добавление в очередь
AddToQueue(task) ==
    /\ CurrentReadyCount < COUNT_IN_READY
    /\ inReady' = [inReady EXCEPT ![task.priority] = Append(inReady[task.priority], task)]

Swap(toPop, toAddToQueue) ==
    inReady' = [inReady EXCEPT
        ![toPop.priority] = Tail(inReady[toPop.priority]),
        ![toAddToQueue.priority] = Append(inReady[toAddToQueue.priority], toAddToQueue)]

\* ready -> running
RunTask(task) ==
    \/ /\ inRunning = <<>>
       /\ PopFromSequence(task)
       /\ Len(inReady[task.priority]) > 0
       /\ inRunning' = Append(inRunning, task)
    \/ /\ inRunning /= <<>>
       /\ Swap(task, inRunning[1])
       /\ inRunning' = <<task>>

\* suspended -> ready
Activate ==
    \E i \in 1..Len(inSuspended):
        /\ inSuspended' = RemoveFromSequenceByIndex(inSuspended, i)
        /\ AddToQueue(inSuspended[i])
        /\ UNCHANGED <<inRunning, inWaiting>>

\* Изменение выполняющейся задачи, реализация логики вытеснения низкоприоритетной задачи
Start ==
    /\ CurrentReadyCount /= 0
    /\ \/ inRunning = <<>>
       \/ /\ inRunning /= <<>>
          /\ \E priority \in PRIORITIES:
                 /\ inReady[priority] /= <<>>
                 /\ inRunning[1].priority < priority

\* running - ready
Preempt ==
    /\ CASE
       (inReady[3] /= <<>>) -> RunTask(inReady[3][1])
       [] (inReady[2] /= <<>>) -> RunTask(inReady[2][1])
       [] (inReady[1] /= <<>>) -> RunTask(inReady[1][1])
       [] (inReady[0] /= <<>>) -> RunTask(inReady[0][1])
       [] OTHER -> FALSE
    /\ UNCHANGED <<inSuspended, inWaiting>>

\* running -> suspended
Terminate ==
    /\ inRunning /= <<>>
    /\ inRunning' = <<>>
    /\ inSuspended' = inSuspended \o inRunning
    /\ UNCHANGED <<inReady, inWaiting>>

\* running -> waiting
Wait ==
    /\ inRunning /= <<>>
    /\ inRunning[1].type = "extended"
    /\ inWaiting' = inWaiting \o inRunning
    /\ inRunning' = <<>>
    /\ UNCHANGED <<inReady, inSuspended>>

\* waiting -> ready
Release ==
    \E i \in 1..Len(inWaiting):
        /\ inWaiting' = RemoveFromSequenceByIndex(inWaiting, i)
        /\ AddToQueue(inWaiting[i])
        /\ UNCHANGED <<inRunning, inSuspended>>

\* Работа системы
Next ==
    \/ /\ Start
       /\ Preempt
    \/ /\ ~Start
       /\ \/ Activate
          \/ Terminate
          \/ Wait
          \/ Release
RunningCountInvariant ==  Len(inRunning) =< 1
CurrentReadyCountInvariant ==  CurrentReadyCount =< COUNT_IN_READY
PriorityInvariant ==
    \/ inRunning = <<>>
    \/ /\ inRunning /= <<>>
       /\ CASE
          (inReady[3] /= <<>> /\ inRunning[1].priority < 3) -> Start
          [] (inReady[2] /= <<>> /\ inRunning[1].priority < 2) -> Start
          [] (inReady[1] /= <<>> /\ inRunning[1].priority < 1) -> Start
          [] OTHER -> TRUE
=============================================================================
