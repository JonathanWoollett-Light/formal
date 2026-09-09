with Ada.Text_IO;
with Ada.Integer_Text_IO;
procedure Rain is
   N : constant := 12;
   type Arr is array (0 .. N - 1) of Integer;
   H : constant Arr := (0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1);
   Left : Integer := 0;
   Right : Integer := N - 1;
   Lmax, Rmax, Total : Integer := 0;
begin
   while Left < Right loop
      if H (Left) < H (Right) then
         if H (Left) >= Lmax then Lmax := H (Left);
         else Total := Total + Lmax - H (Left); end if;
         Left := Left + 1;
      else
         if H (Right) >= Rmax then Rmax := H (Right);
         else Total := Total + Rmax - H (Right); end if;
         Right := Right - 1;
      end if;
   end loop;
   Ada.Integer_Text_IO.Put (Total, Width => 1);
   Ada.Text_IO.New_Line;
end Rain;
