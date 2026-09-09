with Ada.Text_IO;
with Ada.Integer_Text_IO;
procedure Islands is
   Cols : constant := 5;
   Cells : constant := 20;
   type Arr is array (0 .. Cells - 1) of Integer;
   Grid : Arr := (0 | 1 | 5 | 6 | 12 | 18 | 19 => 1, others => 0);
   Stack : Arr;
   Depth : Integer := 0;
   Count : Integer := 0;
   Cell, Col : Integer;

   procedure Visit (C : Integer) is
   begin
      if Grid (C) /= 0 then
         Grid (C) := 0;
         Stack (Depth) := C;
         Depth := Depth + 1;
      end if;
   end Visit;
begin
   for Start in Grid'Range loop
      if Grid (Start) /= 0 then
         Count := Count + 1;
         Grid (Start) := 0;
         Stack (Depth) := Start;
         Depth := Depth + 1;
         while Depth /= 0 loop
            Depth := Depth - 1;
            Cell := Stack (Depth);
            Col := Cell mod Cols;
            if Cell >= Cols then Visit (Cell - Cols); end if;
            if Cell + Cols < Cells then Visit (Cell + Cols); end if;
            if Col /= 0 then Visit (Cell - 1); end if;
            if Col + 1 /= Cols then Visit (Cell + 1); end if;
         end loop;
      end if;
   end loop;
   Ada.Integer_Text_IO.Put (Count, Width => 1);
   Ada.Text_IO.New_Line;
end Islands;
