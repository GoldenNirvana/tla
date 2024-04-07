/--------------------------------- MODULE task ---------------------------------

EXTENDS Integers, Sequences
VARIABLES inReady, inSuspended, inWaiting, isRunning
COUNT == 1
COUNT_IN_READY == 1
PRIORITIES == 0..3
TYPES == { "basic", "extended" }
TASK == [ type: TYPES,  priority: PRIORITIES]

\* Изначально COUNT задач находятся в suspended, и 0 в остальных состояниях
Init ==
    /\ inSuspended \in [1..COUNT -> TASK]
    /\ inReady = [i \in PRIORITIES |-> <<>>]
    /\ isRunning = <<>>
    /\ inWaiting = <<>>

\* Всего задач в ready
CurrentReadyCount == Len(inReady[0]) + Len(inReady[1]) + Len(inReady[2]) + Len(inReady[3])

\* Удаление из очереди по индексу
RemoveFromSequenceByIndex(sequence, index) ==
    IF index <= Len(sequence)
    THEN SubSeq(sequence, 1, index - 1) \o SubSeq(sequence, index + 1, Len(sequence))
    ELSE sequence

\* Добавление в очередь
AddToQueue(task) ==
    /\ CurrentReadyCount < COUNT_IN_READY
    /\ inReady' = [inReady EXCEPT ![task.priority] = Append(inReady[task.priority], task)]

\* Удаление из очереди
Pop(task) ==
    Len(inReady[task.priority]) > 0
    /\ inReady' = [inReady EXCEPT ![task.priority] = SubSeq(inReady[task.priority], 2, Len(inReady[task.priority]))]

Swap(toPop, toAddToQueue) ==
    inReady' = [inReady EXCEPT
        ![toPop.priority] = Tail(inReady[toPop.priority]),
        ![toAddToQueue.priority] = Append(inReady[toAddToQueue.priority], toAddToQueue)]

\* Условие запуска задачи (нет задач на исполнение, или есть более высокоприоритетная задача)
RunTask(task) ==
    \/ /\ isRunning = <<>>
       /\ Pop(task)
       /\ isRunning' = Append(isRunning, task)
    \/ /\ isRunning /= <<>>
       /\ Swap(task, isRunning[1])
       /\ isRunning' = <<task>>


\* Активация задачи, перенос её из suspended
ActivateTransition ==
    \E i \in 1..Len(inSuspended):
        /\ inSuspended' = RemoveFromSequenceByIndex(inSuspended, i)
        /\ AddToQueue(inSuspended[i])
        /\ UNCHANGED <<isRunning, inWaiting>>



\* Изменение выполняющейся задачи, реализация логики вытеснения низкоприоритетной задачи
StartTransition ==
    /\ CurrentReadyCount /= 0
    /\ \/ isRunning = <<>>
       \/ /\ isRunning /= <<>>
          /\ \E priority \in PRIORITIES:
                 /\ inReady[priority] /= <<>>
                 /\ isRunning[1].priority < priority



\* Выбор задачи на выполнение из очереди
PreemptTransition ==
    /\ CASE
       (inReady[3] /= <<>>) -> RunTask(inReady[3][1])
       [] (inReady[2] /= <<>>) -> RunTask(inReady[2][1])
       [] (inReady[1] /= <<>>) -> RunTask(inReady[1][1])
       [] (inReady[0] /= <<>>) -> RunTask(inReady[0][1])
       [] OTHER -> FALSE
    /\ UNCHANGED <<inSuspended, inWaiting>>

\* Завершение задачи
TerminateTransition ==
    /\ isRunning /= <<>>
    /\ isRunning' = <<>>
    /\ inSuspended' = inSuspended \o isRunning
    /\ UNCHANGED <<inReady, inWaiting>>

\* Ожидание задачи (только для расширенных задач)
WaitTransition ==
    /\ isRunning /= <<>>
    /\ isRunning[1].type = "extended"
    /\ inWaiting' = inWaiting \o isRunning
    /\ isRunning' = <<>>
    /\ UNCHANGED <<inReady, inSuspended>>

ReleaseTransition ==
    \E i \in 1..Len(inWaiting):
        /\ inWaiting' = RemoveFromSequenceByIndex(inWaiting, i)
        /\ AddToQueue(inWaiting[i])
        /\ UNCHANGED <<isRunning, inSuspended>>

Next ==
    \/ /\ StartTransition
       /\ PreemptTransition
    \/ /\ ~StartTransition
       /\ \/ ActivateTransition
          \/ TerminateTransition
          \/ WaitTransition
          \/ ReleaseTransition

RunningCountInvariant ==  Len(isRunning) =< 1

CurrentReadyCountInvariant ==  CurrentReadyCount =< COUNT_IN_READY

PriorityInvariant ==
    \/ isRunning = <<>>
    \/ /\ isRunning /= <<>>
       /\ CASE
          (inReady[3] /= <<>> /\ isRunning[1].priority < 3) -> StartTransition
          [] (inReady[2] /= <<>> /\ isRunning[1].priority < 2) -> StartTransition
          [] (inReady[1] /= <<>> /\ isRunning[1].priority < 1) -> StartTransition
          [] OTHER -> TRUE
=============================================================================
