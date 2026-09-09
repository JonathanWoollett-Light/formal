with Ada.Text_IO;
with Ada.Integer_Text_IO;
procedure Intervals is
   N : constant := 4;
   type Arr is array (0 .. N - 1) of Integer;
   Starts : Arr := (2, 1, 15, 8);
   Ends : Arr := (6, 3, 18, 10);
   Outs, Oute : Arr;
   Merged : Integer := 0;
   S, E, T : Integer;
begin
   for Pass in 0 .. N - 1 loop
      for I in 0 .. N - 2 loop
         if Starts (I) > Starts (I + 1) then
            T := Starts (I); Starts (I) := Starts (I + 1); Starts (I + 1) := T;
            T := Ends (I); Ends (I) := Ends (I + 1); Ends (I + 1) := T;
         end if;
      end loop;
   end loop;
   S := Starts (0);
   E := Ends (0);
   for I in 1 .. N - 1 loop
      if Starts (I) <= E then
         if Ends (I) > E then E := Ends (I); end if;
      else
         Outs (Merged) := S; Oute (Merged) := E;
         Merged := Merged + 1;
         S := Starts (I); E := Ends (I);
      end if;
   end loop;
   Outs (Merged) := S; Oute (Merged) := E;
   Merged := Merged + 1;
   for I in 0 .. Merged - 1 loop
      Ada.Integer_Text_IO.Put (Outs (I), Width => 1);
      Ada.Text_IO.Put (" ");
      Ada.Integer_Text_IO.Put (Oute (I), Width => 1);
      Ada.Text_IO.New_Line;
   end loop;
end Intervals;
