### 一种基于分离逻辑的块云存储系统验证工具

在交互式定理证明工具Coq中，我们实现了一个针对块云存储系统（CBS）的验证工具。它具备分离逻辑的关键特性，尤其能支持对CBS程序进行局部推导。

对应实际CBS的主从式架构，工具将CBS细分为两个存储层级:文件层、块层。通过整合内部层级的状态和操作，工具支持表示和验证对实际CBS中的各项数据操作。

#### 工具中证明系统的构建环节

事实上，我们基于分离逻辑，实现了一个关于CBS的证明系统。它涉及到构建建模语言、断言语言、分离逻辑三元组和推理规则等环节。这些环节与工程文件的对应关系如下：

- 建模语言——Language.v

- 断言语言——内部堆谓词（InnerPre.v）+ CBS堆谓词（Himpl.v）

- CBS分离逻辑三元组和推理规则——Rules.v

- 验证实例——Example.v 

工具的实现共涉及3325行代码，其中包括51条定义，242条引理。

此外工具还提供了7个实例的证明，它们分别为：拷贝数据块、移动数据块、清除文件、读取文件内容、向文件尾部添加一个数据块、创建文件、拷贝文件。

#### 工具的开发环境

本工具的开发环境为：

- 操作系统：Windows 10
- Coq版本：Coq 8.8.0
- IDE : vscode

#### 工具的编译方式

##### 1. 安装Coq 8.8.0并配置环境变量

- 安装Coq

​	下载地址：

​	https://github.com/coq/coq/releases/download/V8.8.0/coq-8.8.0-installer-windows-x86_64.exe

​	

完成安装后，需要配置Coq的环境变量：

- 打开环境变量设置

<img src="image\image-20210724145029025.png" alt="avatar" style="zoom:35%;" />

- 在系统变量中，添加Coq的安装路径。

<img src="image\image-20210724145233682.png" alt="avatar" style="zoom:35%;" />

##### 2. 在Windows中安装make编译工具

-  安装终端模拟器Cmder（需要安装full版本，解压后即可使用）


   下载地址：https://cmder.net/

- 以**管理员方式**打开cmder，粘贴如下指令

  - 
    安装软件管理器Chocolatey：

    `@powershell -NoProfile -ExecutionPolicy unrestricted -Command "iex ((new-object net.webclient).DownloadString('https://chocolatey.org/install.ps1'))" && SET PATH=%PATH%;%ALLUSERSPROFILE%\chocolatey\bin`

  - 安装make编译工具：

    `choco install mingw`

##### 3. 在Cmder中，进入到CBSVerifi解压后的文件目录，输入make即可完成编译

<img src="image\image-20210724145814033.png" alt="avatar" style="zoom:50%;" />



最后，可以直接用CoqIDE打开*.v文件，审阅相应的代码。

<img src="image\image-20210724150102388.png" alt="avatar" style="zoom:80%;" />

