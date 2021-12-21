program coordenadas;
uses crt;
var
x,y,z,w: array [1..100] of real;
i,v,b,g :integer;
ch:char;
begin
  textcolor (14);
  textbackground(9);
  clrscr;
  i:= 0;
  g:= 0;
     repeat
      i:= i + 1;
      g:=i;
      writeln;
      write(' digite o valor da Coordenada X  ====>');
      readln ( x[i]);
      writeln;
      write(' Digite o valor da coordenada Y  ====>');
      readln ( y[i]);
      writeln;
      write ( 'Digite o valor da coordenada Z ====>');
      readln (z [i]);
       write ( 'Digite o valor da coordenada W ====>');
      readln (W [i]);

      writeln;
      write( ' deseja digitar o valor de mais alguma coordenada (s/n) ');
      readln(ch);
      clrscr;
    until ( ch = 'n') or ( ch = 'N');
  writeln;
  writeln ('          ษออออออออออออออออออออออออออออออออออออออออออออออออออออออออออป ');
  writeln ('          บ  Coordenada ณ  Coordenada  ณ   Coordenada  ณ Coordenada  บ ');
  writeln ('          บ            ณ             ณ              ณ     x       บ ');
  writeln ('          บ      X      ณ      Y       ณ        Z      ณ     W       บ ');
  writeln ('          ศออออออออออออออออออออออออออออออออออออออออออออออออออออออออออผ ');
  writeln;
  i:=1;
   for i:=1 to g do
          begin
          v:=v+1;
          if i=1 then
          gotoxy (10,8+v);
          writeln(x[i]:3:2);
          gotoxy(35,8+v);
          writeln(y[i]:3:2);
          gotoxy(55,8+v);
          writeln(z[i]:3:2);
          End;
          begin
          if (i>1) and (i<=g) then
          gotoxy(10,8+v);
          writeln(x[i]:3:2);
          gotoxy(35,8+v);
          writeln(y[i]:3:2);
          gotoxy(55,8+v);
          writeln(z[i]:3:2);
          end;
          if ((x[i]) > (x[i-1])) and (i>1) and (i<=g) then
          begin
          gotoxy(1,8+v);
          write('S H');
          end
          else if ((x[i]) < (x[i-1])) and (i>1) and (i<=g) then
          begin
          gotoxy(1,8+v);
          write('A H');
          end;
          if ((y[i]) >  (y[i -1])) and (i >1) and (i<=g) then
          begin
          gotoxy(20,8+v);
          write('S H');
          end
          else if ((y[i]) <  y [i -1]) and (i >1) and (i<=g) then
          begin
          gotoxy(20,8+v);
          write('A H');
          end;
          if ((z[i]) > (z[i-1])) and (i>1) and (i<=g) then
          begin
          gotoxy(40,8+v);
          write('S H');
          end
          else if ((z[i]) < (z[i-1])) and (i>1) and (i<=g) then
          begin
          gotoxy(40,8+v);
          write ('A H');
          end;
          readln;
          end.