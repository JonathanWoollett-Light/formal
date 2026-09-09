with Ada.Text_IO;
with Ada.Integer_Text_IO;
procedure Two_Sum is
   Cap : constant := 8;
   type Nums_Arr is array (0 .. 3) of Integer;
   type Slot_Arr is array (0 .. Cap - 1) of Integer;
   Nums : constant Nums_Arr := (2, 7, 11, 15);
   Target : constant := 9;
   Used, Keys, Vals : Slot_Arr := (others => 0);
   C, H : Integer;
begin
   for I in Nums'Range loop
      C := Target - Nums (I);
      H := ((C mod Cap) + Cap) mod Cap;
      while Used (H) /= 0 loop
         if Keys (H) = C then
            Ada.Integer_Text_IO.Put (Vals (H), Width => 1);
            Ada.Text_IO.Put (" ");
            Ada.Integer_Text_IO.Put (I, Width => 1);
            Ada.Text_IO.New_Line;
            return;
         end if;
         H := (H + 1) mod Cap;
      end loop;
      H := ((Nums (I) mod Cap) + Cap) mod Cap;
      while Used (H) /= 0 loop
         H := (H + 1) mod Cap;
      end loop;
      Used (H) := 1;
      Keys (H) := Nums (I);
      Vals (H) := I;
   end loop;
end Two_Sum;
