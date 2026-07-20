with Ada.Text_IO;
procedure Fannkuch is
   N : constant := 12;
   type Arr is array (0 .. N - 1) of Integer;
   Perm, Cnt, Work : Arr;
   Maxflips : Integer := 0;
   Checksum : Long_Integer := 0;
   Parity : Integer := 0;
   Flips, K, First, I, T : Integer;
begin
   for J in Perm'Range loop Perm (J) := J; Cnt (J) := 0; end loop;
   loop
      Work := Perm;
      Flips := 0;
      loop
         K := Work (0);
         exit when K = 0;
         declare
            A : Integer := 0;
            B : Integer := K;
         begin
            while A < B loop
               T := Work (A); Work (A) := Work (B); Work (B) := T;
               A := A + 1; B := B - 1;
            end loop;
         end;
         Flips := Flips + 1;
      end loop;
      if Flips > Maxflips then Maxflips := Flips; end if;
      if Parity = 0 then Checksum := Checksum + Long_Integer (Flips);
      else Checksum := Checksum - Long_Integer (Flips); end if;
      Parity := 1 - Parity;
      I := 1;
      while I < N loop
         First := Perm (0);
         for J in 0 .. I - 1 loop Perm (J) := Perm (J + 1); end loop;
         Perm (I) := First;
         Cnt (I) := Cnt (I) + 1;
         exit when Cnt (I) <= I;
         Cnt (I) := 0;
         I := I + 1;
      end loop;
      exit when I = N;
   end loop;
   Ada.Text_IO.Put_Line (Long_Integer'Image (Checksum));
   Ada.Text_IO.Put_Line ("Pfannkuchen(" & Integer'Image (N) & " ) =" & Integer'Image (Maxflips));
end Fannkuch;
