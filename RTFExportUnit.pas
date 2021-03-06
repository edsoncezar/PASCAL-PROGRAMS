// PL/SQL Developer (RTF) Export Plug-In
// Copyright 2003 Allround Automations
// support@allroundautomations.com
// http://www.allroundautomations.com

// This demo shows how to add a new export function to PL/SQL Developer
//
// The major export functions are:
//
//  RegisterExport
//  ExportInit
//  ExportFinished
//  ExportPrepare
//  ExportData
//
// for details see plugin.doc


unit RTFExportUnit;

interface

uses
  Windows, Messages, SysUtils, Classes, Graphics, Controls, Forms, Dialogs,
  StdCtrls, Buttons, Grids, ExtCtrls, CheckLst, ComCtrls, Registry,
  ShellAPI, Menus, Variants;

type
  TConfigForm = class(TForm)
    TopPanel: TPanel;
    ButtonPanel: TPanel;
    RightPanel: TPanel;
    OKBtn: TButton;
    CancelBtn: TButton;
    procedure FormCreate(Sender: TObject);
  private
  public
  end;

var
  ConfigForm: TConfigForm = nil;
  PlugInID: Integer;
  ExportPath: string = '';

const // Window types
  wtSQL = 1;
  wtTest = 2;
  wtProcEdit = 3;
  wtCommand = 4;
  wtPlan = 5;

var // Declaration of PL/SQL Developer callback functions
  SYS_Version: function: Integer; cdecl;
  SYS_Registry: function: PChar; cdecl;
  SYS_RootDir: function: PChar; cdecl;
  SYS_OracleHome: function: PChar; cdecl;
  SYS_OCIDLL: function: PChar; cdecl;
  SYS_OCI8Mode: function: Bool; cdecl;

  IDE_MenuState: procedure(ID, Index: Integer; Enabled: Bool); cdecl;
  IDE_SetMenuVisible: procedure(ID, Index: Integer; Enabled: Bool); cdecl;
  IDE_SetMenuCheck: procedure(ID, Index: Integer; Enabled: Bool); cdecl;
  IDE_SetMenuName: procedure(ID, Index: Integer; Name: PChar); cdecl;
  IDE_RefreshMenus: procedure(ID: Integer); cdecl;
  IDE_GetMenuLayout: function: PChar; cdecl;
  IDE_Connected: function: Bool; cdecl;
  IDE_GetConnectionInfo: procedure(var Username, Password, Database: PChar); cdecl;
  IDE_GetBrowserInfo: procedure(var ObjectType, ObjectOwner, ObjectName: PChar); cdecl;
  IDE_GetWindowType: function: Integer; cdecl;
  IDE_GetAppHandle: function: Integer; cdecl;
  IDE_GetWindowHandle: function: Integer; cdecl;
  IDE_GetClientHandle: function: Integer; cdecl;
  IDE_GetChildHandle: function: Integer; cdecl;
  IDE_SaveFile: function: Bool; cdecl;
  IDE_Filename: function: PChar; cdecl;
  IDE_ReloadFile: function: Bool; cdecl;

  IDE_GetCustomKeywords: function: PChar; cdecl;
  IDE_SetCustomKeywords: procedure(Keywords: PChar); cdecl;
  IDE_SetKeywords: procedure(ID, Style: Integer; Keywords: PChar); cdecl;
  IDE_ActivateKeywords: procedure; cdecl;

const // Description of this Plug-In (as displayed in Plug-In configuration dialog)
  Desc = 'RTF Export 1.0';

procedure LoadConfig;
procedure SaveConfig;

implementation

{$R *.DFM}

var
  RTF: string;
  ColCount, CurCol: Integer;
  Prepared: Boolean;
  Header: TStringList;

// RTF Related functions

// Start a group with a {
procedure StartGroup(ControlWord: string = '');
begin
  RTF := RTF + '{';
  if ControlWord <> '' then RTF := RTF + '\' + ControlWord;
end;

// End a group with a }
procedure EndGroup;
begin
  if RTF[Length(RTF)] = ' ' then RTF[Length(RTF)] := '}' else RTF := RTF + '}';
  RTF := RTF + #13#10;
end;

// Start a control word with a /
procedure AddControlWord(Title: string; Value: Variant; Group: Boolean = False);
begin
  if Group then StartGroup(Title) else RTF := RTF + '\' + Title;
  if (VarType(Value) = varString) and (Value <> '') then RTF := RTF + ' ';
  RTF := RTF + string(Value);
  if Group then EndGroup;
end;

// Convert special characters
function RTFString(const S: string): string;
var i: Integer;
begin
  Result := '';
  for i := 1 to Length(S) do
  begin
    case S[i] of
      '}' : Result := Result + '\}';
      '{' : Result := Result + '\{';
      '\' : Result := Result + '\\';
      #10 : Result := Result + #10 + '\par ';
    else
      Result := Result + S[i];
    end;
  end;
end;

// Create the RTF header with some general info
procedure RTFStart(Title, Author, Company: string);
var y, m, d, h, s, ms: Word;
begin
  RTF := '';
  StartGroup('rtf');
  StartGroup('info');
  AddControlWord('title', RTFString(Title), True);
  AddControlWord('author', RTFString(Author), True);
  StartGroup('creatim');
  DecodeDate(Now, y, m, d);
  AddControlWord('yr', y);
  AddControlWord('mo', m);
  AddControlWord('dy', d);
  DecodeTime(Now, h, m, s, ms);
  AddControlWord('hr', h);
  AddControlWord('min', m);
  EndGroup;
  AddControlWord('company', RTFString(Company), True);
  EndGroup;
end;

// Some formating for the rows
procedure RTFFormat1;
begin
  AddControlWord('pard \nowidctlpar\widctlpar\intbl\adjustright', '');
  RTF := RTF + #13#10;
end;

// Some formating, used at the end of the file
procedure RTFFormat2;
begin
  AddControlWord('pard \nowidctlpar\widctlpar\adjustright', '');
  RTF := RTF + #13#10;
end;

// Close the RTF
procedure RTFEnd;
begin
  RTFFormat2;
  AddControlWord('par', '', True);
  EndGroup;
end;

// Start a RTF row
procedure RTFStartRow;
var i: Integer;
begin
  AddControlWord('trowd', '');
  RTF := RTF + #13#10;
  for i := 1 to ColCount do AddControlWord('cellx', Integer(Round(9000 * i / ColCount)));
  RTF := RTF + #13#10;
  RTFFormat1;
  StartGroup;
end;

// Add one cell
procedure RTFAddCell(Value: string);
begin
  RTF := RTF + RTFString(Value);
  AddControlWord('cell ', '');
end;

// End the row
procedure RTFEndRow;
begin
  EndGroup;
  AddControlWord('row', '', True);
end;

// Export related functions

// First call after an export request
// You can ask the user for a filename or initialize stuff.
// Return False if you want to cancel the export.
function ExportInit: Boolean; cdecl;
begin
  ColCount := 0;
  CurCol := 0;
  Prepared := False;
  Result := True;
  Header := TStringList.Create;
  LoadConfig;
end;

// Done, everything is exported.
procedure ExportFinished; cdecl;
var L: TStringList;
    SaveDialog: TSaveDialog;
begin
  RTFEnd;
  L := TStringList.Create;
  try
    SaveDialog := TSaveDialog.Create(nil);
    SaveDialog.Title := 'Export data as RTF';
    SaveDialog.Filter := 'RTF files (*.rtf)|*.rtf|All files (*.*)|*.*';
    SaveDialog.DefaultExt := 'rtf';
    SaveDialog.FileName := '';
    SaveDialog.InitialDir := ExportPath;
    if SaveDialog.Execute then
    begin
      L.Text := RTF;
      L.SaveToFile(SaveDialog.Filename);
      ExportPath := ExtractFilePath(SaveDialog.Filename);
      SaveConfig;
    end;
    SaveDialog.Free;
  except
    on E:Exception do ShowMessage(E.Message);
  end;
  L.Free;
  Header.Free;
end;

// One cell of data, this can be the column description or the actual data.
function ExportData(Value: PChar): Boolean; cdecl;
begin
  Result := True;
  if not Prepared then
  begin
    inc(ColCount);
    Header.Add(Value);
  end else begin
    if CurCol = 0 then RTFStartRow;
    RTFAddCell(Value);
    inc(CurCol);
    if CurCol = ColCount then
    begin
      CurCol := 0;
      RTFEndRow;
    end;
  end;
end;

// This function allows you to prepare for the actual data
// All values received with Exportdata before this function is called are column headers,
// and all values received after ExportPrepare is data.
function ExportPrepare: Boolean; cdecl;
var i: Integer;
begin
  Result := True;
  RTFStart('PL/SQL Developer Export', '', 'Allround Automations');
  RTFFormat1;
  // First add the buffered header
  RTFStartRow;
  for i := 0 to ColCount - 1 do RTFAddCell(Header[i]);
  RTFEndRow;
  Prepared := True;
end;

// Plug-In identification, a unique identifier is received and
// the description is returned
function IdentifyPlugIn(ID: Integer): PChar;  cdecl;
begin
  PlugInID := ID;
  Result := Desc;
end;

// Registration of PL/SQL Developer callback functions
procedure RegisterCallback(Index: Integer; Addr: Pointer); cdecl;
begin
  case Index of
     1 : @SYS_Version := Addr;
     2 : @SYS_Registry := Addr;
     3 : @SYS_RootDir := Addr;
     4 : @SYS_OracleHome := Addr;
     5 : @SYS_OCIDLL := Addr;
     6 : @SYS_OCI8Mode := Addr;
    10 : @IDE_MenuState := Addr;
    11 : @IDE_Connected := Addr;
    12 : @IDE_GetConnectionInfo := Addr;
    13 : @IDE_GetBrowserInfo := Addr;
    14 : @IDE_GetWindowType := Addr;
    15 : @IDE_GetAppHandle := Addr;
    16 : @IDE_GetWindowHandle := Addr;
    17 : @IDE_GetClientHandle := Addr;
    18 : @IDE_GetChildHandle := Addr;
    22 : @IDE_SaveFile := Addr;
    23 : @IDE_Filename := Addr;
    28 : @IDE_ReloadFile := Addr;
    60 : @IDE_GetCustomKeywords := Addr;
    61 : @IDE_SetCustomKeywords := Addr;
    62 : @IDE_SetKeywords := Addr;
    63 : @IDE_ActivateKeywords := Addr;
    64 : @IDE_RefreshMenus := Addr;
    65 : @IDE_SetMenuName := Addr;
    66 : @IDE_SetMenuCheck := Addr;
    67 : @IDE_SetMenuVisible := Addr;
    68 : @IDE_GetMenuLayout := Addr;
  end;
end;

// Load configuration from the registry
procedure LoadConfig;
var Reg: TRegistry;
    Key: string;
 function ReadBool(Name: string): Boolean;
 begin
   try
     Result := Reg.ReadBool(Name);
   except
     Result := False;
   end;
 end;
 function ReadString(Name: string): string;
 begin
   try
     Result := Reg.ReadString(Name);
   except
     Result := '';
   end;
 end;
 function ReadInteger(Name: string): Integer;
 begin
   try
     Result := Reg.ReadInteger(Name);
   except
     Result := 0;
   end;
 end;
begin
  Key := SYS_Registry + '\PlugIns\RTF Export';
  Reg := TRegistry.Create;
  Reg.RootKey := HKEY_CURRENT_USER;
  Reg.OpenKey(Key, False);
  try
    ExportPath := Reg.ReadString('Path');
  except
  end;
  Reg.CloseKey;
  Reg.Free;
end;

// Store configuration in the registry
procedure SaveConfig;
var Key: string;
    Reg: TRegistry;
begin
  Key := SYS_Registry + '\PlugIns\RTF Export';
  Reg := TRegistry.Create;
  Reg.RootKey := HKEY_CURRENT_USER;
  Reg.OpenKey(Key, True);
  Reg.WriteString('Path', ExportPath);
  Reg.CloseKey;
  Reg.Free;
end;

// Called when the Plug-In is created
procedure OnCreate; cdecl;
begin
end;

// Called when the Plug-In is destroyed
procedure OnDestroy; cdecl;
begin
end;

// Display the Configuration form
procedure DoConfigForm;
var Form: TConfigForm;
begin
  Form := TConfigForm.Create(Application);
  with Form do
  begin
    if ShowModal = mrOK then SaveConfig else LoadConfig;
    Free;
  end;
end;


// ConfigForm

procedure TConfigForm.FormCreate(Sender: TObject);
begin
//
end;

function RegisterExport: PChar; cdecl;
begin
  Result := 'RTF File';
end;

// All exported functions
exports
  IdentifyPlugIn,
  RegisterCallback,
  OnCreate,
  OnDestroy,
  RegisterExport,
  ExportInit,
  ExportFinished,
  ExportPrepare,
  ExportData;

end.
