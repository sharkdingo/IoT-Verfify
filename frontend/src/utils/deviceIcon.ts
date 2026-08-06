/**
 * A Material icon name for a device, from its template name.
 *
 * One owner because there were two, and they had drifted in both directions: `DeviceDialog` knew `sprinkler` and
 * `home mode` while `RuleBuilderDialog` did not, and `RuleBuilderDialog` classified `door` as a sensor while
 * `DeviceDialog` did not. The same device therefore drew a different icon depending on which surface you opened —
 * and 48 of the ~51 substring tests were duplicated verbatim between them, so most edits had to be made twice to
 * stay consistent, which is how the three-term gap opened.
 *
 * `door` deliberately does **not** appear on the sensor branch, though `RuleBuilderDialog`'s copy had it there.
 * The first match wins, so listing it as a sensor shadowed the dedicated `garage`/`door` icons further down —
 * `DeviceDialog.spec.ts` asserts those are reachable and caught exactly that when the two copies were merged. The
 * RuleBuilder copy was the wrong one, which is the sort of question only measurement settles.
 *
 * Substring matching on a user-authored template name is inherently approximate; the fallback is the point, not a
 * failure. Order matters: the first match wins, so the narrower terms are tested before the broader ones.
 */
export const deviceIconFor = (templateName?: string | null): string => {

  const name = String(templateName ?? '').toLowerCase()
  
  // 传感器类
  if (name.includes('sensor') || name.includes('temperature') || name.includes('humidity') || name.includes('gas') || name.includes('smoke') || name.includes('motion') || name.includes('soil') || name.includes('illuminance')) {
    return 'sensors'
  }
  
  // 温度/恒温器
  if (name.includes('thermostat') || name.includes('weather')) {
    return 'thermostat'
  }
  
  // 灯/照明
  if (name.includes('light')) {
    return 'lightbulb'
  }
  
  // 开关
  if (name.includes('switch')) {
    return 'toggle_on'
  }
  
  // 空调
  if (name.includes('air conditioner') || name.includes('ac')) {
    return 'ac_unit'
  }
  
  // 空气净化器/通风
  if (name.includes('air purifier') || name.includes('ventilator') || name.includes('humidifier')) {
    return 'air'
  }
  
  // 窗帘/窗户
  if (name.includes('window shade') || name.includes('shade')) {
    return 'blinds'
  }
  if (name.includes('window')) {
    return 'window'
  }
  
  // 门/车库门
  if (name.includes('garage door')) {
    return 'garage'
  }
  if (name.includes('door')) {
    return 'door_front_door'
  }
  
  // 摄像头
  if (name.includes('camera')) {
    return 'videocam'
  }
  
  // 电视
  if (name.includes('tv') || name.includes('television')) {
    return 'tv'
  }
  
  // 手机
  if (name.includes('phone') || name.includes('mobile')) {
    return 'smartphone'
  }
  
  // 洗衣机/烘干机
  if (name.includes('washer') || name.includes('dryer')) {
    return 'local_laundry_service'
  }
  
  // 冰箱
  if (name.includes('refrigerator') || name.includes('fridge')) {
    return 'kitchen'
  }
  
  // 热水器
  if (name.includes('water heater') || name.includes('water')) {
    return 'hot_tub'
  }
  
  // 炊具/烤箱/咖啡机
  if (name.includes('oven') || name.includes('cooker') || name.includes('cooktop')) {
    return 'microwave'
  }
  if (name.includes('coffee')) {
    return 'coffee'
  }
  
  // 警报器
  if (name.includes('alarm') || name.includes('security')) {
    return 'security'
  }
  
  // 汽车
  if (name.includes('car') || name.includes('vehicle')) {
    return 'directions_car'
  }
  
  // 日历/时钟
  if (name.includes('calendar')) {
    return 'calendar_month'
  }
  if (name.includes('clock')) {
    return 'schedule'
  }
  
  // 社交媒体
  if (name.includes('weibo') || name.includes('twitter') || name.includes('facebook') || name.includes('email')) {
    return 'alternate_email'
  }
  
  // 泳池相关
  if (name.includes('pool') || name.includes('sprinkler')) {
    return 'pool'
  }
  
  // 家庭模式
  if (name.includes('home mode') || name.includes('home')) {
    return 'home'
  }
  
  return 'devices_other'
}
