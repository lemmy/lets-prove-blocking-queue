package body Queue with SPARK_Mode is

  protected body Bounded_Queue is
     entry Enqueue(Item : in Element_Type) when Data.Count < Buffer_Size is
     begin
        Data.Buffer(Data.Tail) := Item;
        Data.Tail := (Data.Tail mod Buffer_Size) + 1;
        Data.Count := Data.Count + 1;
     end Enqueue;

     entry Dequeue(Item : out Element_Type) when Data.Count > 0 is
     begin
        Item := Data.Buffer(Data.Head);
        Data.Head := (Data.Head mod Buffer_Size) + 1;
        Data.Count := Data.Count - 1;
     end Dequeue;
  end Bounded_Queue;
end Queue;
