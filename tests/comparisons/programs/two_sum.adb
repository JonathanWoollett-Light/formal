with Ada.Text_IO;
with Ada.Integer_Text_IO;
procedure Two_Sum is
   N : constant := 4;
   Target : constant := 9;
   type Arr is array (0 .. N - 1) of Integer;
   Nums : constant Arr := (2, 7, 11, 15);
   Fi, Fj : Integer := 0;
   Found : Boolean := False;
begin
   for I in Nums'Range loop
      for J in I + 1 .. N - 1 loop
         if Nums (I) + Nums (J) = Target then
            Fi := I; Fj := J; Found := True;
         end if;
      end loop;
   end loop;
   if Found then
      Ada.Integer_Text_IO.Put (Fi, Width => 1);
      Ada.Text_IO.Put (" ");
      Ada.Integer_Text_IO.Put (Fj, Width => 1);
      Ada.Text_IO.New_Line;
   end if;
end Two_Sum;
