<?php
function active($name) {
  return (strpos($_SERVER['PHP_SELF'], $name) !== false) ? 'class="active"' : '';
}
?>

<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN" "http://www.w3.org/TR/html4/strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />
<link rel="stylesheet" type="text/css" href="http://colo1-c703.uibk.ac.at/workspace/new-style-wide.css">
<link rel="stylesheet" type="text/css" href="/software/ttt2/style_experiments.css">
<style rel="stylesheet" type="text/css">
<!--
.subtitle { width: 750px; }
.all { width:1000px; }
.reflection { width:1000px; }
.header { width: 1000px; }
.main_menu { width: 1000px; }
ol { list-style:  decimal; }
.license {
  margin-top: 20px;
  height: 51px;
  background-image: url(img/lgpl.png);
  background-repeat: no-repeat;
}
-->
</style>
<title>Lash-DHOL</title>
</head>

<body>
<div class="lang_sel">
</div>
<div class="all">
<div class="header">
 <div class="subtitle">
  <br/>DHOL version of Lash
 </div>
 <div class="logo"><a href="http://cl-informatik.uibk.ac.at/"></a></div>
</div>

<div class="main_menu">
 <a <?= active('lash-dhol/index.php')?> 
  href="http://cl-informatik.uibk.ac.at/software/lash-dhol/index.php">Home</a>
</div>
