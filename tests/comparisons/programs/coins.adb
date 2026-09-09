with Ada.Text_IO;
with Ada.Integer_Text_IO;
procedure Coins is
   Amount : constant := 11;
   Sentinel : constant := 99;
   type Coin_Arr is array (0 .. 2) of Integer;
   type Dp_Arr is array (0 .. Amount) of Integer;
   Coin : constant Coin_Arr := (1, 2, 5);
   Dp : Dp_Arr := (0 => 0, others => Sentinel);
begin
   for C in Coin'Range loop
      for V in Coin (C) .. Amount loop
         declare
            Cand : constant Integer := Dp (V - Coin (C)) + 1;
         begin
            if Cand < Dp (V) then Dp (V) := Cand; end if;
         end;
      end loop;
   end loop;
   Ada.Integer_Text_IO.Put (Dp (Amount), Width => 1);
   Ada.Text_IO.New_Line;
end Coins;
