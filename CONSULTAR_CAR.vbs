Set WshShell = CreateObject("WScript.Shell")
Set FSO = CreateObject("Scripting.FileSystemObject")

WshShell.CurrentDirectory = FSO.GetParentFolderName(WScript.ScriptFullName)

' Tentar encontrar pythonw.exe em locais comuns
Dim pythonPaths(5)
pythonPaths(0) = WshShell.ExpandEnvironmentStrings("%LOCALAPPDATA%") & "\Programs\Python\Python313\pythonw.exe"
pythonPaths(1) = WshShell.ExpandEnvironmentStrings("%LOCALAPPDATA%") & "\Programs\Python\Python312\pythonw.exe"
pythonPaths(2) = WshShell.ExpandEnvironmentStrings("%USERPROFILE%") & "\miniconda3\pythonw.exe"
pythonPaths(3) = WshShell.ExpandEnvironmentStrings("%USERPROFILE%") & "\anaconda3\pythonw.exe"
pythonPaths(4) = WshShell.ExpandEnvironmentStrings("%LOCALAPPDATA%") & "\anaconda3\pythonw.exe"
pythonPaths(5) = "pythonw.exe"

Dim pythonExe
pythonExe = ""

For Each p In pythonPaths
    If FSO.FileExists(p) Then
        pythonExe = p
        Exit For
    End If
Next

' Fallback: tentar via PATH
If pythonExe = "" Then
    pythonExe = "pythonw.exe"
End If

WshShell.Run """" & pythonExe & """ ""consulta_car_ui.py""", 0, False
