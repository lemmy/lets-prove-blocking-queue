package Queue with SPARK_Mode is

  Buffer_Size : constant := 20;

  type Element_Type is new Integer;
  type Element_Type_Array is array (Integer range <>) of Element_Type;

  type Data_Rec is record
     Buffer : Element_Type_Array(1 .. Buffer_Size) := (others => 0);
     Head, Tail : Natural := 1;
     Count : Natural := 0;
   end record with Predicate => Head in 1 .. Buffer_Size and Tail in 1 .. Buffer_Size;

  protected type Bounded_Queue is
     entry Enqueue(Item : in Element_Type);
     entry Dequeue(Item : out Element_Type);
  private
    Data : Data_Rec;
  end Bounded_Queue ;

end Queue;
