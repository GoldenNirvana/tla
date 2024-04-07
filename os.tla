/--------------------------------- MODULE os ---------------------------------
EXTENDS Integers, Sequences
VARIABLES readyToStartTasks, suspendedTasks, waitingTasks, runningTasks
CONSTANT TASK_COUNT, MAX_READY

Priorities == 0..3
Types == { "simple", "extended" }
Task == [
    type: Types,
    priority: Priorities
]

\* Инициализация модели

Init ==
    readyToStartTasks = [i \in Priorities |-> <<>>]
    /\ runningTasks = <<>>
    /\ waitingTasks = <<>>
    /\ suspendedTasks \in [1..TASK_COUNT -> Task]

\* Подсчет общего размера буфера, позволяет реализовать ограничение на число задач в состоянии ready
ReadyToStartAmount == Len(readyToStartTasks[0]) + Len(readyToStartTasks[1]) + Len(readyToStartTasks[2]) + Len(readyToStartTasks[3])

\* Удаление элемента с индексом из последовательности, необходимо для вытеснения низкоприоритетных задач высокоприоритетными

RemoveIndex(seq, index) ==
    SubSeq(seq, 1, index - 1) \o SubSeq(seq, index + 1, Len(seq))

\* Добавление в очередь

Push(task) ==
    /\ ReadyToStartAmount < MAX_READY
    /\ readyToStartTasks' = [readyToStartTasks EXCEPT ![task.priority] = Append(readyToStartTasks[task.priority], task)]

\* Удаление из очереди

Pop(task) ==
    /\ readyToStartTasks[task.priority] /= <<>>
    /\ readyToStartTasks' = [readyToStartTasks EXCEPT ![task.priority] = Tail(readyToStartTasks[task.priority])]

Swap(toPop, toPush) ==
    readyToStartTasks' = [readyToStartTasks EXCEPT
        ![toPop.priority] = Tail(readyToStartTasks[toPop.priority]),
        ![toPush.priority] = Append(readyToStartTasks[toPush.priority], toPush)]

\* Условие запуска задачи (нет задач на исполнение, или есть более высокоприоритетная задача)

RunTask(task) ==
    \/ /\ runningTasks = <<>>
       /\ Pop(task)
       /\ runningTasks' = Append(runningTasks, task)
    \/ /\ runningTasks /= <<>>
       /\ Swap(task, runningTasks[1])
       /\ runningTasks' = <<task>>

\* Активация задачи, перенос её из suspended

ActivateTransition ==
    \E i \in 1..Len(suspendedTasks):
        /\ suspendedTasks' = RemoveIndex(suspendedTasks, i)
        /\ Push(suspendedTasks[i])
        /\ UNCHANGED <<runningTasks, waitingTasks>>

\* Изменение выполняющейся задачи, реализация логики вытеснения низкоприоритетной задачи

StartTransition ==
    /\ ReadyToStartAmount /= 0
    /\ \/ runningTasks = <<>>
       \/ /\ runningTasks /= <<>>
          /\ \E priority \in Priorities:
                 /\ readyToStartTasks[priority] /= <<>>
                 /\ runningTasks[1].priority < priority

\* Выбор задачи на выполнение из очереди
PreemptTransition ==
    /\ CASE
       (readyToStartTasks[3] /= <<>>) -> RunTask(readyToStartTasks[3][1])
       [] (readyToStartTasks[2] /= <<>>) -> RunTask(readyToStartTasks[2][1])
       [] (readyToStartTasks[1] /= <<>>) -> RunTask(readyToStartTasks[1][1])
       [] (readyToStartTasks[0] /= <<>>) -> RunTask(readyToStartTasks[0][1])
       [] OTHER -> FALSE
    /\ UNCHANGED <<suspendedTasks, waitingTasks>>
\* Завершение задачи
TerminateTransition ==
    /\ runningTasks /= <<>>
    /\ runningTasks' = <<>>
    /\ suspendedTasks' = suspendedTasks \o runningTasks
    /\ UNCHANGED <<readyToStartTasks, waitingTasks>>
\* Ожидание задачи (только для расширенных задач)
WaitTransition ==
    /\ runningTasks /= <<>>
    /\ runningTasks[1].type = "extended"
    /\ waitingTasks' = waitingTasks \o runningTasks
    /\ runningTasks' = <<>>
    /\ UNCHANGED <<readyToStartTasks, suspendedTasks>>

ReleaseTransition ==
    \E i \in 1..Len(waitingTasks):
        /\ waitingTasks' = RemoveIndex(waitingTasks, i)
        /\ Push(waitingTasks[i])
        /\ UNCHANGED <<runningTasks, suspendedTasks>>

Next ==
    \/ /\ StartTransition
       /\ PreemptTransition
    \/ /\ ~StartTransition
       /\ \/ ActivateTransition
          \/ TerminateTransition
          \/ WaitTransition
          \/ ReleaseTransition

RunningCountInvariant ==
    Len(runningTasks) =< 1

ReadyCountInvariant ==
    ReadyToStartAmount =< MAX_READY

PriorityInvariant ==
    \/ runningTasks = <<>>
    \/ /\ runningTasks /= <<>>
       /\ CASE
          (readyToStartTasks[3] /= <<>> /\ runningTasks[1].priority < 3) -> StartTransition
          [] (readyToStartTasks[2] /= <<>> /\ runningTasks[1].priority < 2) -> StartTransition
          [] (readyToStartTasks[1] /= <<>> /\ runningTasks[1].priority < 1) -> StartTransition
          [] OTHER -> TRUE

=============================================================================
