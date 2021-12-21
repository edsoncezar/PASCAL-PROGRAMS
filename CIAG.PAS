program ciag;
var
  c:char;
  n:integer;
begin
  n:=0;
  repeat
    begin
      writeln('Podaj liczbe');
      readln;
      n:=n+1;
      writeln('Czy chcesz kontynuowac {t/n} ?');
      readln(c);
      if (c<>'t') and (c<>'n')
      then writeln('Synkciu kurde czytaj co pisze bo w kly');
    end
  until
    c='n';
  writeln('Ilosc wyrazow w ciagu wynosi ',n);
  readln;
end.