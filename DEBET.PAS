program debett;

var
  placa,suma,x,debet:real;

begin;
  writeln('Podaj place :');
  readln(placa);
  suma:=0;
  repeat
    writeln('Wydatek wynosi :');
    readln(x);
    suma:=suma+x;
  until
    suma>=placa;
  if
    (suma=placa)
  then
    writeln('Wystarczy ci pieniedzy na te wydatki.')
  else
    begin;
      debet:=suma-placa;
      writeln('Twoj debet wynosi : ',debet);
    end;
end.
