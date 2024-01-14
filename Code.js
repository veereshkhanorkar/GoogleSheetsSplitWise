////////////////////////////HEAP Q Implementation///////////////////////////////
var default_cmplt = function(x, y) {
  return x < y;
};

// push an item into heap, O(log n)
function heapq_push(heap, item, cmp) {
  heap.push(item);
  siftdown(heap, 0, heap.length - 1, cmp || default_cmplt);
}
// pop the smallest item from heap, O(log n)
function heapq_pop(heap, cmp) {
  if (heap.length > 0) {
    var last = heap.pop();
    if (heap.length > 0) {
      var head = heap[0];
      heap[0] = last;
      siftup(heap, 0, cmp || default_cmplt);
      return head;
    } else {
      return last;
    }
  }
};
// get the top item, O(1)
function heapq_top(heap){
  if (heap.length !== 0)
    return heap[0];
};
// push an item on the heap and pop out the top item,
// this runs more efficiently than `heapq.push()` followed
// by a separate call to `heapq.pop()`, O(log n)
function pushpop(heap, item, cmp) {
  cmp = cmp || default_cmplt;

  if (heap.length > 0 && cmp(heap[0], item)) {
    var temp = heap[0];
    heap[0] = item;
    item = temp;
    siftup(heap, 0, cmp);
  }
  return item;
};

// transform array `heap` into a heap in-place, O(nlog n)
function heapify(arr, cmp) {
  cmp = cmp || default_cmplt;
  for (var idx = Math.floor(arr.length / 2) - 1;
      idx >= 0; --idx)
    siftup(arr, idx, cmp);
  return arr;
};
// heap sort, O(nlog n)
function heapsort(arr, cmp) {
  var heap = [];

  for (var i = 0; i < arr.length; ++i)
    heapq.push(heap, arr[i], cmp);

  var arr_ = [];

  while (heap.length > 0)
    arr_.push(heapq.pop(heap, cmp));
  return arr_;
};

function siftdown(heap, startIdx, idx, cmp) {
  var item = heap[idx];

  while (idx > startIdx) {
    var parentIdx = (idx - 1) >> 1;
    var parentItem = heap[parentIdx];
    if (cmp(item, parentItem)) {
      heap[idx] = parentItem;
      idx = parentIdx;
      continue;
    }
    break;
  }

  heap[idx] = item;
}

function siftup(heap, idx, cmp) {
  var endIdx = heap.length;
  var startIdx = idx;
  var item = heap[idx];

  var childIdx = idx * 2 + 1;

  while (childIdx < endIdx) {
    var rightIdx = childIdx + 1;

    if (rightIdx < endIdx && (!cmp(
      heap[childIdx], heap[rightIdx]))) {
      childIdx = rightIdx;
    }
    heap[idx] = heap[childIdx];
    idx = childIdx;
    childIdx =  idx * 2 + 1;
  }

  heap[idx] = item;
  siftdown(heap, startIdx, idx, cmp);
}

////////////////////////////HEAP Q Implementation///////////////////////////////

function transpose(a){
  var items = []
  for (var i in a) {
    items.push([i, a[i]])
  }
  return items;
}

function sub_dict(values, from, till, skip_first=false, skip_last=false){
  var data = {};
  var first = true;
  var loop_break = false;
  for(var key in values){
    if (key != from && first == true ){
      continue;
    }
    first = false;
    if (key == till){
      loop_break = true
    }
    data[key] = values[key]
    if (loop_break){
      break;
    }
  }
  if (skip_first){
    var first_item = Object.keys(data)[0];
    delete data[first_item];
  }
  if(skip_last){
    var key_length = Object.keys(data).length;
    var last_item = Object.keys(data)[key_length - 1];
    delete data[last_item];
  }
  return data;
}

var excel = null;

class ExpenseSharing{
  constructor(){
    this.last_modified_time = null;
    this.purchase = null;
    this.participants = null;
    this.item_share = {};
    this.cost_share = {};
    this.simplified = [];
    this.current_dt = new Date();
  }
  get_simplified(){
    return this.simplified;
  }
  simplify(){
    var amt;
    var total = {};
    var giver;
    var receiver;
    for (var i = 0; i < this.spenders.length; i++){
      for (var j = 0; j < this.buyers.length; j++){
        giver = this.spenders[i];
        receiver = this.buyers[j];
        amt = this.to_be_paid(giver, receiver)
        if ( amt == ''){
          continue;
        }
        if ( isNaN(total[giver]) ){
          total[giver] = 0
        }
        if ( isNaN(total[receiver]) ){
          total[receiver] = 0
        }
        total[giver] -= amt
        total[receiver] += amt
      }
    }
    var cmp = function(x, y) {return x[0] < y[0];}
    var credit = [];
    var debit = [];
    for (var name in total){
      var amount = total[name]
      if (amount > 0){
        heapq_push(credit, [-amount, name], cmp)
      }
      if (amount < 0){
        heapq_push(debit, [amount, name], cmp)
      }
    }
    var creditHeap = heapify(credit, cmp)
    var debitHeap = heapify(debit, cmp)
    var amount_left;
    while (creditHeap.length > 0 && debitHeap.length > 0){
      var [credit_value, credit_name] = heapq_pop(creditHeap, cmp);
      var [debit_value, debit_name] = heapq_pop(debitHeap, cmp);
      if (credit_value < debit_value){
        amount_left = credit_value-debit_value
        this.simplified.push([debit_name,credit_name,-1*debit_value])
        heapq_push(creditHeap,[amount_left, credit_name], cmp)
      }else if ( credit_value > debit_value){
        amount_left = debit_value-credit_value
        this.simplified.push([debit_name,credit_name,-1*credit_value])
        heapq_push(debitHeap,[amount_left, debit_name], cmp)
      }else{
        this.simplified.push([debit_name,credit_name,-1*credit_value])
      }
    }
  }

  compute_cost_share(){
    var total_amount = 0.0;
    var total_share = 0.0;
    var share_cost = 0.0;
    var who = null;
    for (var who in this.participants){
      this.cost_share[who] = 0.0;
      for (var i = 0; i < this.participants[who].length; i++){
        total_amount = this.purchase['Amount'][i];
        total_share = this.item_share[i]
        share_cost = total_amount/total_share
        if (this.purchase['Paid By'][i] != who){
          this.cost_share[who] = this.cost_share[who] - (share_cost*(this.participants[who][i]))
        }
        else{
          this.cost_share[who] = this.cost_share[who] + (share_cost*(total_share-this.participants[who][i]))
        }
      }
    }
  }

  recompute(force=false){
    var current_time = this.current_dt.getTime();
    if (this.last_modified_time == null || (current_time - this.last_modified_time > 3) || force){
      var values = rangeToDict(SpreadsheetApp.getActiveSpreadsheet().getSheetByName("Expenses").getDataRange());
      this.purchase = sub_dict(values, "Item", "Paid By");
      // this.purchase = rangeToDict(SpreadsheetApp.getActiveSpreadsheet().getSheetByName("Expenses").getRange("A:D"));
      this.participants = sub_dict(values, "Paid By", "Per Share", true, true);
      // this.participants = rangeToDict(SpreadsheetApp.getActiveSpreadsheet().getSheetByName("Expenses").getRange("E:N"));
      this.buyers = Array.from(new Set(this.purchase['Paid By']))
      this.spenders = Array.from(Object.keys(this.participants))
      this.compute_item_total_share();
      this.last_modified_time = current_time;
      this.simplify();
      this.compute_cost_share();
    }
  }

  owed_amount(who){
    return this.cost_share[who];
  }

  compute_item_total_share(){
    var total = 0.0;
    for (var i = 0; i < this.purchase['Item'].length; i++){
      total = 0.0;
      for (var j in this.participants){
        if ( this.participants[j][i] == null){
          continue
        }
        total = this.participants[j][i] + total;
      }
      this.item_share[i] = total;
    }
  }

  to_be_paid(who, whom){
    if (who == whom || who == '' || whom == ''){
      return '';
    }
    var total_amount = 0.0;
    var net_amount = 0.0;
    var total_share = 0.0;
    for (var i = 0; i < this.purchase['Amount'].length; i++){
      if (this.purchase['Paid By'][i] != whom){
        continue;
      }
      total_amount = this.purchase['Amount'][i];
      total_share = this.item_share[i]
      net_amount = net_amount + ((total_amount/total_share)*(this.participants[who][i]))
    }
    return net_amount;
  }
}

function init_data(){
  if (excel == null){
    excel = new ExpenseSharing();
    excel.recompute()
  }
}

function owed_amount(who){
  if (who == ""){
    return who;
  }
  init_data()
  return excel.owed_amount(who);
}

function to_be_paid(who, whom){
  init_data();
  return excel.to_be_paid(who, whom);
}

function calculate_share(total, share_range) {
  var shares = 0.0, parsed_value = 0.0;
  for (var r = 0; r < share_range.length; r++) {
    for (var c = 0; c < share_range[r].length; c++) {
      parsed_value = parseFloat(share_range[r][c]);
      if (!isNaN(parsed_value)) {
        shares = parsed_value + shares;
      }
    }
  }
  if (shares > 0){
    return total/shares;
  }
  return '';
}

function rangeToDict(sheet) {
  var columns = sheet.getValues()[0];
  var data = sheet.getValues();
  var dict_data = {};
  for (var i = 0; i < columns.length; i++) {
    dict_data[columns[i]] = [];
    for (var j=1; j < data.length; j++ ){
      if (data[j][i].length == 0){
        continue;
      }
      dict_data[columns[i]].push(data[j][i])
    }
  }
  return dict_data;
}

function recompute(){
  init_data();
}

function simplified(){
  init_data();
  var obj = excel.get_simplified();
  const cell = SpreadsheetApp.getActiveSheet().getCurrentCell();
  SpreadsheetApp.getActiveSheet().getRange(
    cell.getRow(),cell.getColumn(), obj.length, obj[0].length
  ).setValues(obj);
}



