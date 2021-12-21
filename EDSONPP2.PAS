program coordenadasfinal;
uses crt;

var

  a,b,c,d,AX,BX,CX,DX,AAx,BBx,CCx,DDx,AA,BB,CC,DD
  ,AA1,AA2,BB1,BB2,CC1,CC2,DD1,DD2:array[1..100] of real;
  i,k:integer;
  CH:CHAR;


  sentido:char;
  bit1,bit2,bit3,bit4,bit5,bit6,bit7,bit8:byte;


  ia,tempoint:integer;
  RPM,RPMa,pulsoi,tempoi,tempo,pulsos,ka,z
  ,resultadozero,voltasmin, idivid20:real;

  ib,tempointb:integer;
  RPMb,RPMab,pulsoib,tempoib,tempob,pulsosb,kb,zb
  ,resultadozerob,voltasminb, idivid20b:real;

  ic,tempointc:integer;
  RPMc,RPMac,pulsoic,tempoic,tempoc,pulsosc,kc,zc
  ,resultadozeroc,voltasminc, idivid20c: real;


  id,tempointd:integer;
  RPMd,RPMad,pulsoid,tempoid,tempod,pulsosd,kd,zd
  ,resultadozerod,voltasmind, idivid20d: real;

const
data=$378;
{status= data+1;
control=data+2}

begin
k:=0;
i:=0;
textcolor(14);
textbackground(1);
clrscr;

  repeat
  clrscr;
  i:=i + 1;
  k:=k + 1;


begin
textcolor(14);
textbackground(1);
clrscr;
writeln('');writeln('');writeln('');writeln('');



  gotoxy(2,2);
  write('DIGITE COORDENADA A');
  writeln;
  gotoxy(28,2);
  readln(A[i]);

  repeat
  textcolor(14);

  gotoxy(35,2);
    write('ROTA€ÇO RPMa(max=900)=>');
      gotoxy(60,2);
        readln(RPMa);
  RPM:=RPMa*1;
  until(RPMa<=900);


  gotoxy(2,4) ;
  write('DIGITE COORDENADA B');
  writeln;
  gotoxy(28,4);
  readln(B[i]);

  repeat
  gotoxy(35,4);
    write('ROTA€ÇO RPMb(max=900)=>');
      gotoxy(60,4);
        readln(RPMab);
  RPMb:=RPMab*1;
  until(RPMb<=900);


  gotoxy(2,6);
  write('DIGITE COORDENADA C');
  writeln;
  gotoxy(28,6);
  readln(C[i]);


  repeat
  textcolor(14);
  gotoxy(35,6);
    write('ROTA€ÇO RPMc(max=900)=>');
      gotoxy(60,6);
        readln(RPMac);
          RPMc:=RPMac*1;
  until(RPMc<=900);
  end;

  gotoxy(2,8);
  write ('DIGITE COORDENADA D');
  writeln;
  gotoxy(28,8);
  readln(D[i]);


  repeat
  textcolor(14);
  gotoxy(35,8);
    write('ROTA€ÇO RPMd(max=900)=>');
      gotoxy(60,8);
        readln(RPMad);
RPMd:=RPMad*1;
until(RPMd<=900);




  repeat
  gotoxy(20,10);
  write('DESEJA DIGITAR MAIS ALGUM NUMERO (S/N)');
  gotoxy(40,12);
  readln(ch);



  until  (ch ='n') or (ch ='N') or (ch ='s') or (ch ='S');
  until (ch ='n') or (ch ='N') ;
  clrscr;


  I:=0;
  for i := 1 to k do

  begin
  gotoxy(1,2);
  write('   ============A===========B===========C===========D============');

  gotoxy(14,4+i);
  write('',A[i]:3:2);

  AA[i] := A[i] - A[i-1];
  {AX[i] := A[i] - A[i+1];}

  if i = 1 then
  write ('          ');



  if AA[i] = 0 then
  write ('  MP  ')
    else if AA[i] > 0 then
    write ('   H')
      else if AA[i] < 0 then
      write ('  AH');


                 {    if AA[i] = 0 then
                      write ('  MP  ')
                      else if  AA[i]  > A[i] then
                      write ( '  H')
                      else if AA[i] < A[i] then
                      write ('  AH'); }



                      AAx[i] := abs (AA[i]);

            {if  AA[i] > 0 then AA[i]:= AA1[i]
                else if AA[i] < 0  then AA[i] := AA2[i];}

  gotoxy(26,4+i);
  write('',B[i]:3:2);

  BB[i] := B[i] - B[i-1];
  {BX[i] := B[i] - B[i+i];}

  if i = 1 then
  write ('          ');

  if BB[i] = 0 then
  write ('  MP  ')
    else if BB[i] > 0 then
    write ('   H')
      else if BB[i] < 0 then
      write ('  AH');


                   {   if BB[i] = 0 then
                       write ('  MP  ')
                       else if BB[i] > B[i] then
                       write ( '  H')
                       else if BB[i] < B[i] then
                       write ('  AH');   }


                      BBx[i] := abs (BB[i]);

          {if  BB[i] > 0 then BB[i]:= BB1[i]
              else if BB[i] < 0  then BB[i] := BB2[i];}

  gotoxy(38,4+i);
  write('',C[i]:3:2);

  CC[i] := C[i] - C[i-1];
  {CX[i] := C[i] - C[i+1];}

  if i = 1 then
  write ('          ');

  if CC[i] = 0 then
  write ('  MP  ')
    else if CC[i] > 0 then
    write ('   H')
      else if CC[i] < 0 then
      write ('  AH');

                       {   if CC[i] = 0 then
                           write ('  MP  ')
                           else if CC[i] > C[i] then
                           write ( '  H')
                           else if CC[i] < C[i] then
                           write ('  AH');    }

                           CCx[i] := abs (CC[i]);

              {if  CC[i] > 0 then CC[i]:= CC1[i]
                  else if CC[i] < 0  then CC[i] := CC2[i];}

  gotoxy(50,4+i);
  write('',D[i]:3:2);
  DD[i] := D[i] - D[i-1];
  {DX[i] := D[i] - D[i+1];}

  if i = 1 then
  write ('                                                                 ');

  if DD[i] = 0 then
  write ('  MP  ')
    else if DD[i] > 0 then
    write ('   H')
      else if DD[i] < 0 then
      write ('  AH');

                    {   if DD[i] = 0 then
                        write ('  MP                                                             ')
                        else if DD[i] > D[i] then
                        write ( '  H')
                        else if DD[i] < D[i] then
                        write ('  AH');   }


                    DDx[i] := abs (DD[i]);

           {if  DD[i] > 0 then DD[i]:= DD1[i]
               else if DD[i] < 0  then DD[i] := DD2[i];}
  end;


tempo:=(1000/(RPM/3));
tempoi:=int(tempo);
pulsos:=AAx[i]*20;
pulsoi:=int(pulsos);
tempoint:=trunc(tempoi);
ia:=1;

while (ia<pulsoi) do
begin

  if AA[i] = 0 then port[data] := 0
     else if AA[i] > 0  then port[data] :=1
       else if AA[i] < 0 then port[data] := 3;

delay(tempoint);
port[data]:=0;
delay(tempoint);
write('Ü');
ia:=ia+1;
resultadozero:=ia mod 20;
idivid20:=ia/20;
if resultadozero=0 then write ('',idivid20:1:0,'');
end;


tempob:=(1000/(RPMb/3));
tempoib:=int(tempob);
pulsosb:=BBx[i]*20;
pulsoib:=int(pulsosb);
tempointb:=trunc(tempoib);
ib:=1;
while (ib<pulsoib) do
begin


  if BB[i] = 1 then port[data] := 0
     else if BB[i] > 0 then port[data] :=4
       else if BB[i] < 0 then port[data] := 12;

delay(tempointb);
port[data]:=0;
delay(tempoint);
write('­');
ib:=ib+1;
resultadozerob:=ib mod 20;
idivid20b:=ib/20;
if resultadozerob=0 then write ('',idivid20b:1:0,'');
end;


tempoc:=(1000/(RPMc/3));
tempoic:=int(tempoc);
pulsosc:=CCx[i]*20;
pulsoic:=int(pulsosc);
tempointc:=trunc(tempoic);
ic:=1;
while (ic<pulsoic) do

begin

  if CC[i] = 1 then port[data] := 0
     else if CC[i] > 0 then port[data] :=16
       else if CC[i] < 0 then port[data] := 48;


delay (tempointc);

port[data]:=0;
delay(tempointc);

write('þ');
ic:=ic+1;
resultadozeroc:=ic mod 20;
idivid20c:=ic/20;
if resultadozeroc=0 then write ('',idivid20c:1:0,'');
end;


tempod:=(1000/(RPMd/3));
tempoid:=int(tempod);
pulsosd:=DDx[i]*20;
pulsoid:=int(pulsosd);
tempointd:=trunc(tempoid);
i:=1;
while (i<pulsoid) do
begin

   if DD[i] = 1 then port[data] := 0
     else if DD[i] > 0 then port[data] :=64
       else if DD[i] < 0 then port[data] := 192;

delay(tempointd);
port[data]:=0;
delay(tempointd);

write('');
i:=i+1;
resultadozerod:=i mod 20;
idivid20d:=id/20;
if resultadozerod=0 then write ('',idivid20d:1:0,'');
end;
{port[data]:=bit3;
bit3:=0;}
DELAY(4000);
CLRSCR;
begin
sound(750);
delay(250);
sound(1000);
delay(250);
sound(1250);
delay(250);
nosound;

TEXTCOLOR(120);

gotoxy(20,5);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');

TEXTCOLOR(121);
gotoxy(20,6);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');

TEXTCOLOR(122);
gotoxy(20,7);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');

TEXTCOLOR(123);
gotoxy(20,8);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');

TEXTCOLOR(124);
gotoxy(20,9);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');

TEXTCOLOR(125);
gotoxy(20,10);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');

TEXTCOLOR(126);
gotoxy(20,11);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');

TEXTCOLOR(127);
gotoxy(20,12);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');

TEXTCOLOR(128);
gotoxy(20,13);
write('APERTE QQ TC PARA ENCERRAR O PROGRAMA');
READKEY;

end;
end.